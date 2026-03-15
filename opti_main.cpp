/*
 * ═══════════════════════════════════════════════════════════════
 * WORD SEARCH PUZZLE SOLVER
 * ═══════════════════════════════════════════════════════════════
 *
 * Problem:
 *   Given a grid of width x height cells:
 *   1. Place all "required" words (marked with "+") somewhere on the grid
 *      in any of 8 directions (N, NE, E, SE, S, SW, W, NW)
 *   2. Fill all remaining empty cells with lowercase letters
 *   3. Ensure no "forbidden" words (marked with "-") appear anywhere
 *      on the completed grid in any direction
 *   4. Output one solution or all unique solutions
 *
 * Input format (from file argv[1]):
 *   width height
 *   + required_word     (must appear on the board)
 *   - forbidden_word    (must NOT appear anywhere)
 *
 * Output: written to file argv[2]
 * Mode:   argv[3] = "one_solution" or "all_solutions"
 *
 * Algorithm overview:
 *   Phase 1 — Place required words using backtracking with a
 *             conflict matrix for constraint propagation. Words
 *             sorted by MRV (fewest placement options first).
 *   Phase 2 — Fill remaining empty cells using backtracking with:
 *             - English letter-frequency ordering (common letters first)
 *             - Trie-based forbidden word detection (is_safe)
 *             - Periodic forward checking for dead-spot detection
 */

#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <cstring>
#include <bitset>

using namespace std;

// ═══════════════════════════════════════════════════════════════
// TRIE DATA STRUCTURE — stores forbidden words for fast lookup
// ═══════════════════════════════════════════════════════════════
//
// Flat-array layout for cache friendliness:
//   trie_children[node * 26 + char_index] = child node index
//   Zero means "no child at this character".
//   Node 0 is always the root.
//
// Why flat arrays instead of pointer-based nodes?
//   - Better cache locality: children of a node are contiguous in memory
//   - No pointer-chasing: direct index arithmetic
//   - Dynamically grown so we don't waste memory on small inputs

static const int TRIE_INIT_CAP = 8192;   // initial node capacity
int* trie_children = nullptr;            // flat child array
bool* trie_end     = nullptr;            // does a forbidden word end at this node?
int trie_cap   = 0;                      // current allocated capacity (nodes)
int trie_count = 1;                      // next free node (0 = root, always exists)

// Grow trie storage when we need more nodes
void trie_grow(int need) {
    if (need <= trie_cap) return;
    int new_cap = max(trie_cap * 2, need);
    // Allocate new zero-initialized arrays
    int*  nc = new int [new_cap * 26]();
    bool* ne = new bool[new_cap]();
    // Copy old data if it exists
    if (trie_children) {
        memcpy(nc, trie_children, trie_cap * 26 * sizeof(int));
        memcpy(ne, trie_end,      trie_cap * sizeof(bool));
        delete[] trie_children;
        delete[] trie_end;
    }
    trie_children = nc;
    trie_end      = ne;
    trie_cap      = new_cap;
}

// Insert a single forbidden word into the trie
void insert_forbidden(const string& s) {
    trie_grow(trie_count + (int)s.length() + 1);
    int curr = 0;
    for (char c : s) {
        int slot = curr * 26 + (c - 'a');
        if (!trie_children[slot]) {
            trie_grow(trie_count + 1);
            trie_children[slot] = trie_count++;
        }
        curr = trie_children[slot];
    }
    trie_end[curr] = true;
}

// ═══════════════════════════════════════════════════════════════
// GRID AND GLOBAL STATE
// ═══════════════════════════════════════════════════════════════

static const int MAX_CELLS = 2601;  // supports up to 51x51 grids
char grid[MAX_CELLS];               // the board (row-major, '.' = empty)
int width, height, total_cells;
int max_f_len = 0;                  // length of longest forbidden word
bool one_solution_mode;              // true = stop after finding first solution

// 8 direction vectors: N, NE, E, SE, S, SW, W, NW
static const int dx[] = {-1, -1,  0,  1, 1, 1, 0, -1};
static const int dy[] = { 0,  1,  1,  1, 0,-1,-1, -1};

// Letters ordered by English frequency (most common first).
// Trying 'e' before 'z' finds valid fill-letters faster on average.
static const char freq_order[] = "etaoinshrdlcumwfgypbvkjxqz";

// ═══════════════════════════════════════════════════════════════
// REQUIRED WORD PLACEMENT DATA
// ═══════════════════════════════════════════════════════════════

// Compact placement descriptor: row, col, direction index
struct Placement { short row, col; char dir; };

vector<string>              required_words;   // the words that must appear
vector<vector<Placement>>   word_placements;  // all valid positions per word

// Solution storage
bool           found_one = false;
string         single_solution;    // used in one_solution mode
vector<string> solutions;          // used in all_solutions mode

// ═══════════════════════════════════════════════════════════════
// CONFLICT MATRIX — constraint propagation for required words
// ═══════════════════════════════════════════════════════════════
//
// conflict_matrix[word_i][placement_p][word_j] is a bitset where
// bit k = 1 means placement k of word j is COMPATIBLE with
// placement p of word i.
//
// Two placements CONFLICT when they use the same grid cell but
// want different letters there. By AND-ing future word domains
// with the conflict mask, we prune impossible placements early,
// often eliminating huge branches of the search tree.
//
// Built using a cell-indexed approach:
//   1. For each cell, record all (word, placement, letter) entries
//   2. At each cell, mark pairs with different letters as conflicting
//   This is O(total_cells × avg_entries²) — much faster than the
//   naive O(words² × placements² × wordlen²).

static const int MAX_P = 1024;   // max placements tracked per word
typedef bitset<MAX_P> Mask;
Mask*** conflict_matrix = nullptr;

void build_conflict_matrix(int n) {
    // --- Step 1: Build cell → entries map ---
    // For each grid cell, record which (word, placement, letter) use it
    struct CellEntry { short word, placement; char letter; };
    vector<vector<CellEntry>> cell_map(total_cells);

    for (int i = 0; i < n; ++i) {
        const string& w = required_words[i];
        int len = (int)w.length();
        for (int p = 0; p < (int)word_placements[i].size() && p < MAX_P; ++p) {
            const Placement& pl = word_placements[i][p];
            int rdx = dx[(int)pl.dir], rdy = dy[(int)pl.dir];
            for (int k = 0; k < len; ++k) {
                int cell = (pl.row + rdx * k) * width + (pl.col + rdy * k);
                cell_map[cell].push_back({(short)i, (short)p, w[k]});
            }
        }
    }

    // --- Step 2: Allocate masks (all bits set = "fully compatible") ---
    conflict_matrix = new Mask**[n];
    for (int i = 0; i < n; ++i) {
        int pi = min((int)word_placements[i].size(), MAX_P);
        conflict_matrix[i] = new Mask*[pi];
        for (int p = 0; p < pi; ++p) {
            conflict_matrix[i][p] = new Mask[n];
            for (int j = 0; j < n; ++j)
                conflict_matrix[i][p][j].set();  // start: all compatible
        }
    }

    // --- Step 3: Mark conflicting pairs ---
    // Two entries at the same cell from different words with different
    // letters means those placements are mutually incompatible.
    for (int cell = 0; cell < total_cells; ++cell) {
        auto& entries = cell_map[cell];
        for (size_t a = 0; a < entries.size(); ++a) {
            for (size_t b = a + 1; b < entries.size(); ++b) {
                if (entries[a].word   == entries[b].word)   continue; // same word
                if (entries[a].letter == entries[b].letter) continue; // no conflict
                // Mark as incompatible in both directions
                conflict_matrix[entries[a].word][entries[a].placement][entries[b].word]
                    .reset(entries[b].placement);
                conflict_matrix[entries[b].word][entries[b].placement][entries[a].word]
                    .reset(entries[a].placement);
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════
// FORBIDDEN WORD CHECKER — is_safe(row, col)
// ═══════════════════════════════════════════════════════════════
//
// After placing a letter at (row, col), check whether any forbidden
// word now appears passing through that cell in any direction.
//
// How it works:
//   For each of 8 directions, we consider every possible starting
//   position for a forbidden word that includes (row, col):
//     - A word of length L starting at offset k before (row,col)
//       means the starting cell is (row - dx*k, col - dy*k)
//     - k ranges from 0 to max_f_len - 1
//   From each valid starting position, walk forward through the
//   trie up to max_f_len characters. If we hit a trie end node,
//   a forbidden word is present → return false (unsafe).
//
// Complexity: O(8 × max_f_len × max_f_len) per cell in the worst
// case, but trie mismatches cause early exit in practice.

static inline bool is_safe(int row, int col) {
    for (int dir = 0; dir < 8; ++dir) {
        int rdx = dx[dir], rdy = dy[dir];

        for (int offset = 0; offset < max_f_len; ++offset) {
            // Starting position for this window
            int sr = row - rdx * offset;
            int sc = col - rdy * offset;
            if (sr < 0 || sr >= height || sc < 0 || sc >= width) continue;

            // Walk forward through the trie from this start
            int node = 0;
            int cr = sr, cc = sc;
            for (int i = 0; i < max_f_len; ++i) {
                if (cr < 0 || cr >= height || cc < 0 || cc >= width) break;
                char ch = grid[cr * width + cc];
                if (ch == '.') break;   // empty cell breaks the letter sequence

                int next = trie_children[node * 26 + (ch - 'a')];
                if (!next) break;       // no trie path → no forbidden word here
                node = next;

                if (trie_end[node]) return false;  // FORBIDDEN WORD DETECTED

                cr += rdx;
                cc += rdy;
            }
        }
    }
    return true;  // no forbidden words pass through this cell
}

// ═══════════════════════════════════════════════════════════════
// PHASE 2: FILL REMAINING EMPTY CELLS
// ═══════════════════════════════════════════════════════════════
//
// After all required words are placed, fill every '.' cell with a
// letter such that no forbidden word is created.
//
// Optimizations:
//   - Try letters in English frequency order (finds solutions faster)
//   - Forward checking: periodically scan ahead for "dead spots"
//     (cells where no letter is safe → branch is hopeless)
//   - Early exit in one_solution mode once a solution is found

// Check if the next empty cell after start_pos has no valid letter.
// If so, this branch is a dead end. Only checks ONE cell ahead
// to keep the overhead low (full lookahead is too expensive).
bool has_dead_spot(int start_pos) {
    for (int p = start_pos + 1; p < total_cells; ++p) {
        if (grid[p] == '.') {
            int row = p / width, col = p % width;
            // Try every letter; if any works, not a dead spot
            for (int i = 0; i < 26; ++i) {
                grid[p] = freq_order[i];
                if (is_safe(row, col)) { grid[p] = '.'; return false; }
            }
            grid[p] = '.';
            return true;  // no letter works here → dead spot
        }
    }
    return false;  // no empty cells ahead
}

// Recursively fill empty cells from position pos onward
void fill_grid(int pos) {
    if (one_solution_mode && found_one) return;

    // Skip over already-filled cells
    while (pos < total_cells && grid[pos] != '.') ++pos;

    if (pos == total_cells) {
        // Board is complete → record this solution
        string sol(grid, total_cells);
        if (one_solution_mode) {
            single_solution = sol;
            found_one = true;
        } else {
            solutions.push_back(sol);
        }
        return;
    }

    // Periodic forward check: when many cells remain, occasionally
    // verify the next empty cell still has at least one valid letter.
    // The thresholds (12 cells remaining, every 4th position) balance
    // dead-end detection benefit against the cost of the check.
    if (total_cells - pos > 12 && (pos & 3) == 0 && has_dead_spot(pos))
        return;

    int row = pos / width, col = pos % width;

    // Try each letter in frequency order
    for (int i = 0; i < 26; ++i) {
        grid[pos] = freq_order[i];
        if (is_safe(row, col)) fill_grid(pos + 1);
        if (one_solution_mode && found_one) { grid[pos] = '.'; return; }
    }
    grid[pos] = '.';  // undo: backtrack
}

// ═══════════════════════════════════════════════════════════════
// PHASE 1: PLACE REQUIRED WORDS
// ═══════════════════════════════════════════════════════════════
//
// Recursively try each placement for each required word.
// Uses the conflict matrix for constraint propagation:
//   When word i is placed at position p, AND the domain of each
//   future word j with conflict_matrix[i][p][j]. If any future
//   word's domain becomes empty, this branch is a dead end.
//
// After all required words are placed, calls fill_grid() for
// the remaining empty cells.

vector<Mask> domains;  // domains[i] = bitmask of still-valid placements for word i

void solve_required(int idx) {
    if (one_solution_mode && found_one) return;

    if (idx == (int)required_words.size()) {
        // All required words placed → fill remaining empty cells
        fill_grid(0);
        return;
    }

    const string& w = required_words[idx];
    int len = (int)w.length();
    Mask& active = domains[idx];

    // Try each placement that hasn't been pruned
    for (int p_idx = 0; p_idx < (int)word_placements[idx].size() && p_idx < MAX_P; ++p_idx) {
        if (one_solution_mode && found_one) return;
        if (!active.test(p_idx)) continue;  // pruned by constraint propagation

        const Placement& p = word_placements[idx][p_idx];
        int rdx = dx[(int)p.dir], rdy = dy[(int)p.dir];

        // --- Check compatibility: existing letters must match or be empty ---
        bool can_place = true;
        for (int i = 0; i < len; ++i) {
            char ex = grid[(p.row + rdx * i) * width + (p.col + rdy * i)];
            if (ex != '.' && ex != w[i]) { can_place = false; break; }
        }
        if (!can_place) continue;

        // --- Place the word, recording changes for backtracking ---
        int changed[MAX_CELLS];
        int change_count = 0;
        bool safe = true;

        for (int i = 0; i < len; ++i) {
            int cr = p.row + rdx * i, cc = p.col + rdy * i;
            int cell = cr * width + cc;
            if (grid[cell] == '.') {
                grid[cell] = w[i];
                changed[change_count++] = cell;
                // Check that placing this letter doesn't form a forbidden word
                if (!is_safe(cr, cc)) { safe = false; break; }
            }
        }

        if (safe) {
            // --- Constraint propagation: narrow future word domains ---
            // By AND-ing with the conflict mask for this choice, we remove
            // placements of future words that are incompatible.
            struct DomainUndo { int word; Mask old_mask; };
            vector<DomainUndo> undo;
            bool dead_end = false;

            for (int nw = idx + 1; nw < (int)required_words.size(); ++nw) {
                Mask old_mask = domains[nw];
                domains[nw] &= conflict_matrix[idx][p_idx][nw];
                if (domains[nw] != old_mask)
                    undo.push_back({nw, old_mask});
                if (domains[nw].none()) { dead_end = true; break; }
            }

            if (!dead_end) solve_required(idx + 1);

            // Undo domain changes
            for (auto it = undo.rbegin(); it != undo.rend(); ++it)
                domains[it->word] = it->old_mask;
        }

        // Undo grid changes
        for (int i = 0; i < change_count; ++i) grid[changed[i]] = '.';
    }
}

// ═══════════════════════════════════════════════════════════════
// MAIN
// ═══════════════════════════════════════════════════════════════

int main(int argc, char* argv[]) {
    // Speed up I/O by disabling synchronization with C stdio
    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);

    if (argc < 4) return 1;
    ifstream infile(argv[1]);
    ofstream outfile(argv[2]);
    one_solution_mode = (strcmp(argv[3], "one_solution") == 0);

    // Initialize trie with starting capacity
    trie_grow(TRIE_INIT_CAP);

    // Read grid dimensions and initialize all cells as empty ('.')
    infile >> width >> height;
    total_cells = width * height;
    memset(grid, '.', total_cells);

    // ── Parse input: required words (+) and forbidden words (-) ──
    string type, val;
    while (infile >> type >> val) {
        if (type == "+") {
            required_words.push_back(val);
        } else {
            // Track the longest forbidden word (limits our scan range in is_safe)
            if ((int)val.length() > max_f_len) max_f_len = (int)val.length();
            // Insert the word AND its reverse, because words can be read
            // backwards on the board (e.g., "cat" reversed is "tac")
            insert_forbidden(val);
            string rev(val.rbegin(), val.rend());
            insert_forbidden(rev);
        }
    }

    // ── Pre-compute all valid placements for each required word ──
    // A placement is valid if the word fits entirely within the grid bounds.
    int n = (int)required_words.size();
    word_placements.resize(n);
    vector<pair<int, int>> meta(n);  // (placement_count, original_index)

    for (int i = 0; i < n; ++i) {
        int len = (int)required_words[i].length();
        auto& opts = word_placements[i];
        for (int row = 0; row < height; ++row)
            for (int col = 0; col < width; ++col)
                for (int dir = 0; dir < 8; ++dir) {
                    // Check if the word's last letter stays in bounds
                    int er = row + dx[dir] * (len - 1);
                    int ec = col + dy[dir] * (len - 1);
                    if (er >= 0 && er < height && ec >= 0 && ec < width)
                        opts.push_back({(short)row, (short)col, (char)dir});
                }
        meta[i] = {(int)opts.size(), i};
    }

    // ── Sort words by MRV (Minimum Remaining Values) ──
    // Place the most constrained words first (fewest valid positions).
    // This causes earlier pruning and dramatically reduces search time.
    sort(meta.begin(), meta.end());

    // Reorder words and placements according to MRV order
    vector<string>             sw(n);
    vector<vector<Placement>>  sp(n);
    for (int i = 0; i < n; ++i) {
        sw[i] = move(required_words[meta[i].second]);
        sp[i] = move(word_placements[meta[i].second]);
    }
    required_words  = move(sw);
    word_placements = move(sp);

    // ── Build conflict matrix for constraint propagation ──
    // This precomputes which placement pairs are incompatible,
    // enabling fast domain narrowing during the search.
    if (n > 0) {
        build_conflict_matrix(n);
        // Initialize domains: every placement is initially valid
        domains.resize(n);
        for (int i = 0; i < n; ++i) {
            int pi = min((int)word_placements[i].size(), MAX_P);
            for (int p = 0; p < pi; ++p) domains[i].set(p);
        }
    }

    // ── Solve ──
    solve_required(0);

    // ═══════════════════════════════════════════════════════════
    // OUTPUT RESULTS
    // ═══════════════════════════════════════════════════════════

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
        // Deduplicate: different placement orders can yield the same board
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

    // ── Cleanup ──
    delete[] trie_children;
    delete[] trie_end;
    if (conflict_matrix) {
        for (int i = 0; i < n; ++i) {
            int pi = min((int)word_placements[i].size(), MAX_P);
            for (int p = 0; p < pi; ++p) delete[] conflict_matrix[i][p];
            delete[] conflict_matrix[i];
        }
        delete[] conflict_matrix;
    }

    return 0;
}
