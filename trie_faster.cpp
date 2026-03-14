#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <cstring>
#include <bitset>
#include <unordered_set>
#include <unordered_map>
#include <array>
#include <cstdint>

using namespace std;

// MAX_P: Maximum possible locations a single word can fit on the board.
// Mask: A bitset "checklist" to track which placements are still valid.
const int MAX_P = 1024;
typedef bitset<MAX_P> Mask;

struct Placement {
    vector<int> pos;    // cell indices this placement covers
    string vals;        // letters placed at those cells
};

struct TrieNode {
    int children[26];
    bool is_end;
    TrieNode() { memset(children, -1, sizeof(children)); is_end = false; }
};
vector<TrieNode> trie;

void insert_forbidden(const string& s) {
    int curr = 0;
    for (char c : s) {
        int v = c - 'a';
        if (trie[curr].children[v] == -1) {
            trie[curr].children[v] = trie.size();
            trie.push_back(TrieNode());
        }
        curr = trie[curr].children[v];
    }
    trie[curr].is_end = true;
}

int width, height, total_cells;
char grid[2601];
string mode;
vector<string> req_words;
vector<vector<Placement>> choices;
unordered_set<string> unique_boards; // faster than set for large collections

int dx[] = {-1, -1, 0, 1, 1, 1, 0, -1};
int dy[] = {0, 1, 1, 1, 0, -1, -1, -1};

// Maximum forbidden word length (used to limit scan range)
int max_forbidden_len = 0;

// ============================================================
// Incremental forbidden word check: only checks paths through
// a specific cell, and only walks up to max_forbidden_len steps.
// This replaces both creates_forbidden() and final_safety_check().
// ============================================================
bool creates_forbidden_at(int pos) {
    int row = pos / width, col = pos % width;
    for (int dir = 0; dir < 8; ++dir) {
        // We need to check all starting points along this direction
        // that could produce a word passing through (row, col).
        // A forbidden word of length L starting at offset -k from (row,col)
        // means we start at (row - k*dx, col - k*dy) and the word passes through here.
        // Instead of that complex logic, we check both this direction and its reverse
        // starting FROM this cell. But that misses words that start before this cell
        // and end after it.
        //
        // Correct approach: walk backwards along direction up to max_forbidden_len-1
        // steps to find the earliest possible start, then scan forward.
        
        // Find the earliest start cell along this direction that could
        // produce a forbidden word passing through (row, col).
        int sr = row, sc = col;
        for (int back = 0; back < max_forbidden_len - 1; ++back) {
            int nr = sr - dx[dir], nc = sc - dy[dir];
            if (nr < 0 || nr >= height || nc < 0 || nc >= width) break;
            if (grid[nr * width + nc] == '.') break;
            sr = nr; sc = nc;
        }
        
        // Now scan forward from (sr, sc) in direction dir, checking trie
        int curr = 0;
        int r = sr, c = sc;
        while (r >= 0 && r < height && c >= 0 && c < width) {
            char ch = grid[r * width + c];
            if (ch == '.') break;
            int v = ch - 'a';
            if (trie[curr].children[v] == -1) break;
            curr = trie[curr].children[v];
            if (trie[curr].is_end) return true;
            r += dx[dir]; c += dy[dir];
        }
    }
    return false;
}

// Check forbidden words at a specific cell AND all its neighbors
// (placing a letter can complete words that pass through neighboring cells)
bool creates_forbidden_near(int pos) {
    if (creates_forbidden_at(pos)) return true;
    int row = pos / width, col = pos % width;
    for (int d = 0; d < 8; ++d) {
        int nr = row + dx[d], nc = col + dy[d];
        if (nr >= 0 && nr < height && nc >= 0 && nc < width && grid[nr * width + nc] != '.') {
            if (creates_forbidden_at(nr * width + nc)) return true;
        }
    }
    return false;
}

// ============================================================
// Constraint propagation for fill_remaining:
// For each empty cell, track which letters (a-z) are still valid.
// Use MRV (minimum remaining values) to pick the most constrained
// cell first, and propagate constraints incrementally.
// ============================================================

// Check if placing letter 'c' at position 'pos' would create a forbidden word
bool letter_creates_forbidden(int pos, char c) {
    char old = grid[pos];
    grid[pos] = c;
    bool bad = creates_forbidden_near(pos);
    grid[pos] = old;
    return bad;
}

// Domain: which letters are still possible for each empty cell
// We use a bitmask of 26 bits for efficiency
uint32_t cell_domain[2601]; // bitmask of valid letters per cell
int domain_size[2601];      // popcount cache

void fill_remaining_opt(vector<int>& empty_cells, int remaining) {
    if (remaining == 0) {
        unique_boards.insert(string(grid, total_cells));
        return;
    }

    // MRV heuristic: pick the empty cell with fewest valid letters
    int best = -1, best_size = 27;
    for (int i = 0; i < (int)empty_cells.size(); ++i) {
        int pos = empty_cells[i];
        if (grid[pos] != '.') continue; // already filled
        if (domain_size[pos] < best_size) {
            best_size = domain_size[pos];
            best = i;
            if (best_size == 0) return; // dead end - no valid letters
            if (best_size == 1) break;  // can't do better
        }
    }
    if (best == -1) return;

    int pos = empty_cells[best];
    uint32_t dom = cell_domain[pos];

    while (dom) {
        int bit = __builtin_ctz(dom); // index of lowest set bit
        dom &= dom - 1;              // clear lowest set bit
        char c = 'a' + bit;

        grid[pos] = c;

        // Check forbidden words near this cell
        if (creates_forbidden_near(pos)) {
            grid[pos] = '.';
            continue;
        }

        // Forward-check: update domains of neighboring empty cells
        // and record changes for undo
        struct Change { int pos; uint32_t old_domain; int old_size; };
        vector<Change> changes;
        bool dead_end = false;

        // Collect neighbors that might be affected (within max_forbidden_len radius)
        for (int i = 0; i < (int)empty_cells.size() && !dead_end; ++i) {
            int npos = empty_cells[i];
            if (npos == pos || grid[npos] != '.') continue;

            // Only recompute domains for cells close enough to be affected
            int nr = npos / width, nc = npos % width;
            int pr = pos / width, pc = pos % width;
            int dist = max(abs(nr - pr), abs(nc - pc));
            if (dist > max_forbidden_len) continue;

            uint32_t old_dom = cell_domain[npos];
            int old_sz = domain_size[npos];
            uint32_t new_dom = 0;
            uint32_t check = old_dom;
            while (check) {
                int b = __builtin_ctz(check);
                check &= check - 1;
                if (!letter_creates_forbidden(npos, 'a' + b)) {
                    new_dom |= (1u << b);
                }
            }
            if (new_dom != old_dom) {
                changes.push_back({npos, old_dom, old_sz});
                cell_domain[npos] = new_dom;
                domain_size[npos] = __builtin_popcount(new_dom);
                if (new_dom == 0) { dead_end = true; }
            }
        }

        if (!dead_end) {
            fill_remaining_opt(empty_cells, remaining - 1);
        }

        // Undo domain changes
        for (auto& ch : changes) {
            cell_domain[ch.pos] = ch.old_domain;
            domain_size[ch.pos] = ch.old_size;
        }

        grid[pos] = '.';
        if (mode == "one_solution" && !unique_boards.empty()) return;
    }
}

// ============================================================
// Conflict detection using cell-indexed lookup instead of
// O(n^2 * P^2 * L^2) brute force.
// For each cell, store which (word_idx, placement_idx, char) use it.
// Two placements conflict if they use the same cell with different chars.
// ============================================================

// conflicts_allowed[i][p][j] = mask of placements of word j compatible
// with placement p of word i. Built using cell-indexed approach.
Mask*** conflicts = nullptr;

void build_conflicts_fast(int n) {
    // Step 1: Build cell -> list of (word_idx, placement_idx, letter) map
    // Use a flat vector per cell for cache friendliness
    struct CellEntry { short word; short placement; char letter; };
    vector<vector<CellEntry>> cell_map(total_cells);

    for (int i = 0; i < n; ++i) {
        for (int p = 0; p < (int)choices[i].size() && p < MAX_P; ++p) {
            for (size_t k = 0; k < choices[i][p].pos.size(); ++k) {
                int cell = choices[i][p].pos[k];
                cell_map[cell].push_back({(short)i, (short)p, choices[i][p].vals[k]});
            }
        }
    }

    // Step 2: Allocate conflict masks - only for actual placement count
    conflicts = new Mask**[n];
    for (int i = 0; i < n; ++i) {
        int pi = min((int)choices[i].size(), MAX_P);
        conflicts[i] = new Mask*[pi];
        for (int p = 0; p < pi; ++p) {
            conflicts[i][p] = new Mask[n];
            for (int j = 0; j < n; ++j) conflicts[i][p][j].set(); // start: all compatible
        }
    }

    // Step 3: For each cell, find conflicting placement pairs
    for (int cell = 0; cell < total_cells; ++cell) {
        auto& entries = cell_map[cell];
        // Sort by word index for grouping
        // For each pair of entries from different words at this cell
        // with different letters, mark as conflicting
        for (size_t a = 0; a < entries.size(); ++a) {
            for (size_t b = a + 1; b < entries.size(); ++b) {
                auto& ea = entries[a];
                auto& eb = entries[b];
                if (ea.word == eb.word) continue;      // same word, skip
                if (ea.letter == eb.letter) continue;   // same letter, no conflict
                // These two placements conflict
                conflicts[ea.word][ea.placement][eb.word].reset(eb.placement);
                conflicts[eb.word][eb.placement][ea.word].reset(ea.placement);
            }
        }
    }
}

// ============================================================
// solve_required with in-place domain modification + undo stack
// ============================================================
vector<Mask> domains_global;

void solve_required(int w_idx) {
    if (w_idx == (int)req_words.size()) {
        vector<int> empty_cells;
        for (int i = 0; i < total_cells; ++i)
            if (grid[i] == '.') empty_cells.push_back(i);

        if (empty_cells.empty()) {
            // No empty cells - just check for forbidden words at all filled positions
            bool bad = false;
            for (int i = 0; i < total_cells && !bad; ++i)
                if (creates_forbidden_at(i)) bad = true;
            if (!bad) unique_boards.insert(string(grid, total_cells));
        } else {
            // Initialize domains for empty cells
            for (int pos : empty_cells) {
                cell_domain[pos] = 0;
                for (int b = 0; b < 26; ++b) {
                    if (!letter_creates_forbidden(pos, 'a' + b)) {
                        cell_domain[pos] |= (1u << b);
                    }
                }
                domain_size[pos] = __builtin_popcount(cell_domain[pos]);
            }
            fill_remaining_opt(empty_cells, (int)empty_cells.size());
        }
        return;
    }

    Mask& active = domains_global[w_idx];
    for (int p_idx = 0; p_idx < (int)choices[w_idx].size() && p_idx < MAX_P; ++p_idx) {
        if (!active.test(p_idx)) continue;

        const auto& p = choices[w_idx][p_idx];
        bool overlap_fail = false;

        // Verify word can fit with existing letters
        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] != '.' && grid[p.pos[i]] != p.vals[i]) {
                overlap_fail = true;
                break;
            }
        }
        if (overlap_fail) continue;

        // Place word, record changes for undo
        vector<pair<int, char>> grid_memo;
        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] == '.') {
                grid_memo.push_back({p.pos[i], '.'});
                grid[p.pos[i]] = p.vals[i];
            }
        }

        // In-place domain update with undo recording
        struct DomainUndo { int word; Mask old_mask; };
        vector<DomainUndo> undo_stack;
        bool dead_end = false;

        for (int n_w = w_idx + 1; n_w < (int)req_words.size(); ++n_w) {
            Mask old_mask = domains_global[n_w];
            domains_global[n_w] &= conflicts[w_idx][p_idx][n_w];
            if (domains_global[n_w] != old_mask) {
                undo_stack.push_back({n_w, old_mask});
            }
            if (domains_global[n_w].none()) { dead_end = true; break; }
        }

        if (!dead_end) solve_required(w_idx + 1);

        // Undo domain changes
        for (auto it = undo_stack.rbegin(); it != undo_stack.rend(); ++it) {
            domains_global[it->word] = it->old_mask;
        }

        // Undo grid changes
        for (auto& m : grid_memo) grid[m.first] = m.second;
        if (mode == "one_solution" && !unique_boards.empty()) return;
    }
}

int main(int argc, char* argv[]) {
    if (argc < 4) return 1;
    ios::sync_with_stdio(0);
    cin.tie(0);
    ifstream in(argv[1]);
    ofstream out(argv[2]);
    mode = argv[3];

    if (!(in >> width >> height)) return 0;
    total_cells = width * height;
    memset(grid, '.', total_cells);
    trie.push_back(TrieNode());

    string t, v;
    while (in >> t >> v) {
        if (t == "+") {
            req_words.push_back(v);
        } else {
            insert_forbidden(v);
            if ((int)v.length() > max_forbidden_len)
                max_forbidden_len = v.length();
            string r = v;
            reverse(r.begin(), r.end());
            if (r != v) insert_forbidden(r);
        }
    }

    // Sort longest to shortest (longer words are more constrained)
    sort(req_words.begin(), req_words.end(), [](const string& a, const string& b) {
        return a.length() > b.length();
    });

    int n = req_words.size();
    choices.resize(n);
    vector<Mask> initial_domains(n);

    // Precalculate every placement for every word
    for (int i = 0; i < n; ++i) {
        int len = req_words[i].length();
        for (int row = 0; row < height; row++)
            for (int col = 0; col < width; col++)
                for (int dir = 0; dir < 8; dir++) {
                    int end_row = row + dx[dir] * (len - 1);
                    int end_col = col + dy[dir] * (len - 1);
                    if (end_row >= 0 && end_row < height && end_col >= 0 && end_col < width) {
                        Placement p;
                        p.pos.reserve(len);
                        p.vals.reserve(len);
                        for (int k = 0; k < len; k++) {
                            p.pos.push_back((row + dx[dir] * k) * width + (col + dy[dir] * k));
                            p.vals.push_back(req_words[i][k]);
                        }
                        choices[i].push_back(p);
                        if ((int)choices[i].size() <= MAX_P)
                            initial_domains[i].set(choices[i].size() - 1);
                    }
                }
    }

    // Build conflict matrix using cell-indexed approach (much faster)
    build_conflicts_fast(n);

    // Use global domains for in-place modification
    domains_global = initial_domains;
    solve_required(0);

    if (unique_boards.empty()) {
        out << "No solutions found" << endl;
        return 0;
    }

    if (mode == "one_solution") {
        out << "Board:" << endl;
        const string& s = *unique_boards.begin();
        for (int i = 0; i < height; ++i) {
            out << "  ";
            for (int j = 0; j < width; ++j) out << s[i * width + j];
            out << endl;
        }
    } else {
        out << unique_boards.size() << " solution(s)" << endl;
        for (const string& s : unique_boards) {
            out << "Board:" << endl;
            for (int i = 0; i < height; ++i) {
                out << "  ";
                for (int j = 0; j < width; ++j) out << s[i * width + j];
                out << endl;
            }
        }
    }
    return 0;
}