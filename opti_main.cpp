#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <cstring>

using namespace std;

// ── Trie: compact allocation ────────────────────────────────────────
// Instead of a flat 300K*26 array (~31MB), allocate nodes on demand.
// Each node is 26 child indices (int16_t) + 1 end flag = 53 bytes vs 104.
// We use int for child indices to avoid overflow for large dictionaries,
// but cap at a reasonable max. Actual memory = trie_count * 26 * sizeof(int).

static const int TRIE_INIT_CAP = 8192;   // grow dynamically
int* trie_children = nullptr;             // trie_children[node*26 + c]
bool* trie_end_flag = nullptr;
int trie_cap = 0;
int trie_count = 1; // 0 = root

void trie_ensure_cap(int need) {
    if (need <= trie_cap) return;
    int new_cap = max(trie_cap * 2, need);
    int* nc = new int[new_cap * 26]();          // zero-initialized
    bool* ne = new bool[new_cap]();
    if (trie_children) {
        memcpy(nc, trie_children, trie_cap * 26 * sizeof(int));
        memcpy(ne, trie_end_flag, trie_cap * sizeof(bool));
        delete[] trie_children;
        delete[] trie_end_flag;
    }
    trie_children = nc;
    trie_end_flag = ne;
    trie_cap = new_cap;
}

// ── Grid constants ──────────────────────────────────────────────────
static const int MAX_DIM = 2601;
char grid[MAX_DIM];
int width, height, total_cells;
int max_f_len = 0;
bool one_solution_mode;  // bool instead of string comparison in hot path

// Direction vectors (8 directions)
static const int dx[] = {-1, -1, 0, 1, 1, 1, 0, -1};
static const int dy[] = {0, 1, 1, 1, 0, -1, -1, -1};

// Letter frequency order for backtracking heuristic
static const char alpha[] = "etaoinshrdlcumwfgypbvkjxqz";

struct Placement { short row, col; char dir; };

vector<string> required_words;
vector<vector<Placement>> word_placements;

// For one_solution mode, store only one; for all_solutions, collect into set
bool found_one = false;
string single_solution;
vector<string> solutions;

// ── Trie operations ─────────────────────────────────────────────────
void insert_forbidden(const string& s) {
    int len = (int)s.length();
    if (len > max_f_len) max_f_len = len;
    trie_ensure_cap(trie_count + len + 1);
    int curr = 0;
    for (char c : s) {
        int idx = c - 'a';
        int slot = curr * 26 + idx;
        if (!trie_children[slot]) {
            trie_ensure_cap(trie_count + 1);
            trie_children[slot] = trie_count++;
        }
        curr = trie_children[slot];
    }
    trie_end_flag[curr] = true;
}

// ── Optimized is_safe ────────────────────────────────────────────────
// For each of 8 directions,
// check all windows of length up to max_f_len that INCLUDE (row,col).
// A window starts at offset 0..max_f_len-1 cells BEFORE (row,col).
// For each starting offset, walk the trie until mismatch or end.
// This is what the original did but we eliminate redundant in_bounds
// calls and the unused valid_window variable.

static inline bool is_safe_v2(int row, int col) {
    for (int dir = 0; dir < 8; ++dir) {
        int rdx = dx[dir], rdy = dy[dir];
        for (int offset = 0; offset < max_f_len; ++offset) {
            int sr = row - rdx * offset;
            int sc = col - rdy * offset;

            if (sr < 0 || sr >= height || sc < 0 || sc >= width) continue;

            int node = 0;
            int cr = sr, cc = sc;
            for (int i = 0; i < max_f_len; ++i) {
                if (cr < 0 || cr >= height || cc < 0 || cc >= width) break;

                char ch = grid[cr * width + cc];
                if (ch == '.') break;

                int next = trie_children[node * 26 + (ch - 'a')];
                if (!next) break;       // no trie path, skip rest
                node = next;

                if (trie_end_flag[node]) return false;

                cr += rdx;
                cc += rdy;
            }
        }
    }
    return true;
}

// ── Forward checking (lightweight) ──────────────────────────────────
// Only check the NEXT empty cell. Skip the expensive heuristic if
// we're close to the end (few cells left).
bool has_future_deadspot(int start_pos) {
    for (int p = start_pos + 1; p < total_cells; ++p) {
        if (grid[p] == '.') {
            int row = p / width, col = p % width;
            for (int i = 0; i < 26; ++i) {
                grid[p] = alpha[i];
                if (is_safe_v2(row, col)) { grid[p] = '.'; return false; }
            }
            grid[p] = '.';
            return true; // no letter works → dead spot
        }
    }
    return false;
}

// ── Fill remaining empty cells ──────────────────────────────────────
void fill_grid(int pos) {
    if (one_solution_mode && found_one) return;

    // Skip to next empty cell (iterative, not recursive, for filled cells)
    while (pos < total_cells && grid[pos] != '.') ++pos;

    if (pos == total_cells) {
        string sol(grid, total_cells);
        if (one_solution_mode) {
            single_solution = sol;
            found_one = true;
        } else {
            solutions.push_back(sol);
        }
        return;
    }

    // Forward check: only when enough cells remain and periodically
    if (total_cells - pos > 12 && (pos & 3) == 0 && has_future_deadspot(pos)) return;

    int row = pos / width, col = pos % width;
    for (int i = 0; i < 26; ++i) {
        grid[pos] = alpha[i];
        if (is_safe_v2(row, col)) fill_grid(pos + 1);
        if (one_solution_mode && found_one) { grid[pos] = '.'; return; }
    }
    grid[pos] = '.';
}

// ── Place required words recursively ────────────────────────────────
void solve_required(int idx) {
    if (one_solution_mode && found_one) return;
    if (idx == (int)required_words.size()) {
        fill_grid(0);
        return;
    }

    const string& w = required_words[idx];
    int len = (int)w.length();
    int changed[MAX_DIM];

    for (const Placement& p : word_placements[idx]) {
        if (one_solution_mode && found_one) return;

        int rdx = dx[(int)p.dir], rdy = dy[(int)p.dir];
        bool can_place = true;
        for (int i = 0; i < len; ++i) {
            char ex = grid[(p.row + rdx * i) * width + (p.col + rdy * i)];
            if (ex != '.' && ex != w[i]) { can_place = false; break; }
        }
        if (!can_place) continue;

        int count = 0;
        bool safe = true;
        for (int i = 0; i < len; ++i) {
            int cr = p.row + rdx * i, cc = p.col + rdy * i;
            int idx_1d = cr * width + cc;
            if (grid[idx_1d] == '.') {
                grid[idx_1d] = w[i];
                changed[count++] = idx_1d;
                if (!is_safe_v2(cr, cc)) { safe = false; break; }
            }
        }
        if (safe) solve_required(idx + 1);
        // Undo
        for (int i = 0; i < count; ++i) grid[changed[i]] = '.';
    }
}

// ── Main ────────────────────────────────────────────────────────────
int main(int argc, char* argv[]) {
    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);

    if (argc < 4) return 1;
    ifstream infile(argv[1]);
    ofstream outfile(argv[2]);
    one_solution_mode = (strcmp(argv[3], "one_solution") == 0);

    // Initialize trie
    trie_ensure_cap(TRIE_INIT_CAP);

    infile >> width >> height;
    total_cells = width * height;
    memset(grid, '.', total_cells);

    string type, val;
    while (infile >> type >> val) {
        if (type == "+") {
            required_words.push_back(val);
        } else {
            insert_forbidden(val);
            string rev(val.rbegin(), val.rend()); // slightly cleaner reverse
            insert_forbidden(rev);
        }
    }

    // Pre-compute valid placements and sort words by fewest options (MRV)
    int n = (int)required_words.size();
    word_placements.resize(n);
    vector<pair<int, int>> meta(n);

    for (int i = 0; i < n; ++i) {
        int len = (int)required_words[i].length();
        vector<Placement>& opts = word_placements[i];
        for (int row = 0; row < height; ++row) {
            for (int col = 0; col < width; ++col) {
                for (int dir = 0; dir < 8; ++dir) {
                    int er = row + dx[dir] * (len - 1);
                    int ec = col + dy[dir] * (len - 1);
                    if (er >= 0 && er < height && ec >= 0 && ec < width)
                        opts.push_back({(short)row, (short)col, (char)dir});
                }
            }
        }
        meta[i] = {(int)opts.size(), i};
    }

    sort(meta.begin(), meta.end());

    // Reorder by MRV
    vector<string> sw(n);
    vector<vector<Placement>> sp(n);
    for (int i = 0; i < n; ++i) {
        sw[i] = move(required_words[meta[i].second]);
        sp[i] = move(word_placements[meta[i].second]);
    }
    required_words = move(sw);
    word_placements = move(sp);

    solve_required(0);

    // Output
    if (one_solution_mode) {
        if (!found_one) {
            outfile << "No solutions found\n";
        } else {
            outfile << "Board:\n";
            for (int i = 0; i < height; ++i) {
                outfile << "  ";
                outfile.write(single_solution.data() + i * width, width);
                outfile << '\n';
            }
        }
    } else {
        // Deduplicate
        sort(solutions.begin(), solutions.end());
        solutions.erase(unique(solutions.begin(), solutions.end()), solutions.end());

        if (solutions.empty()) {
            outfile << "No solutions found\n";
        } else {
            outfile << solutions.size() << " solution(s)\n";
            for (const string& s : solutions) {
                outfile << "Board:\n";
                for (int i = 0; i < height; ++i) {
                    outfile << "  ";
                    outfile.write(s.data() + i * width, width);
                    outfile << '\n';
                }
            }
        }
    }

    delete[] trie_children;
    delete[] trie_end_flag;
    return 0;
}