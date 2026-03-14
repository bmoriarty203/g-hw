#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <cstring>
#include <bitset>
#include <unordered_set>

using namespace std;

const int MAX_P = 1024;
typedef bitset<MAX_P> Mask;

struct Placement {
    vector<int> pos;
    string vals;
};

// Hash set for forbidden words
unordered_set<string> forbidden_words;

// Simple function to add forbidden words
void insert_forbidden(const string& s) {
    forbidden_words.insert(s);
    string r = s;
    reverse(r.begin(), r.end());
    if (r != s) {
        forbidden_words.insert(r);  // Add reversed version too
    }
}

int width, height, total_cells;
char grid[2601];
string mode;
vector<string> req_words;
vector<vector<Placement>> choices;
unordered_set<string> unique_boards;
Mask*** conflicts = nullptr;
vector<vector<Mask>> domain_stack;  // NEW: Domain stack for efficient backtracking

int dx[] = {-1, -1, 0, 1, 1, 1, 0, -1};
int dy[] = {0, 1, 1, 1, 0, -1, -1, -1};

// OPTIMIZED: Incremental forbidden word check (only check words touching this cell)
bool creates_forbidden_incremental(int row, int col) {
    if (grid[row * width + col] == '.') return false;
    
    for (int dir = 0; dir < 8; ++dir) {
        string word = "";
        
        // Extend backward from this position
        int back_r = row - dx[dir];
        int back_c = col - dy[dir];
        while (back_r >= 0 && back_r < height && back_c >= 0 && back_c < width && 
               grid[back_r * width + back_c] != '.') {
            word = grid[back_r * width + back_c] + word;
            back_r -= dx[dir];
            back_c -= dy[dir];
        }
        
        // Add current letter
        word += grid[row * width + col];
        
        // Extend forward
        int fwd_r = row + dx[dir];
        int fwd_c = col + dy[dir];
        while (fwd_r >= 0 && fwd_r < height && fwd_c >= 0 && fwd_c < width && 
               grid[fwd_r * width + fwd_c] != '.') {
            word += grid[fwd_r * width + fwd_c];
            fwd_r += dx[dir];
            fwd_c += dy[dir];
        }
        
        // Only check words of length >= 2
        if (word.length() >= 2 && forbidden_words.count(word)) {
            return true;
        }
    }
    return false;
}

// Full board check (only called when board is complete)
bool final_safety_check() {
    for (int row = 0; row < height; ++row) {
        for (int col = 0; col < width; ++col) {
            if (creates_forbidden_incremental(row, col)) return true;
        }
    }
    return false;
}

// OPTIMIZED: Use incremental check and avoid full copies
void fill_remaining(int cell_idx, const vector<int>& empty_cells) {
    if (cell_idx == (int)empty_cells.size()) {
        if (!final_safety_check()) {
            unique_boards.insert(string(grid, total_cells));
        }
        return;
    }

    int pos = empty_cells[cell_idx];
    int row = pos / width, col = pos % width;
    
    for (char c = 'a'; c <= 'z'; ++c) {
        grid[pos] = c;
        // OPTIMIZED: Only check this cell, not the entire board
        if (!creates_forbidden_incremental(row, col)) {
            fill_remaining(cell_idx + 1, empty_cells);
            if (mode == "one_solution" && !unique_boards.empty()) {
                grid[pos] = '.';
                return;
            }
        }
    }
    grid[pos] = '.';
}

// OPTIMIZED: Pass domains by reference and use domain stack
void solve_required(int w_idx) {
    if (w_idx == (int)req_words.size()) {
        vector<int> empty_cells;
        for (int i = 0; i < total_cells; ++i) {
            if (grid[i] == '.') empty_cells.push_back(i);
        }
        
        if (empty_cells.empty()) {
            if (!final_safety_check()) {
                unique_boards.insert(string(grid, total_cells));
            }
        } else {
            fill_remaining(0, empty_cells);
        }
        return;
    }

    // Get current domains from stack
    vector<Mask>& current_domains = domain_stack.back();
    Mask active = current_domains[w_idx];
    
    for (int p_idx = 0; p_idx < (int)choices[w_idx].size(); ++p_idx) {
        if (!active.test(p_idx)) continue;  // Skip inactive placements

        const auto& p = choices[w_idx][p_idx];
        bool overlap_fail = false;
        vector<pair<int, char>> memo;

        // Verify word can fit with existing letters
        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] != '.' && grid[p.pos[i]] != p.vals[i]) {
                overlap_fail = true;
                break;
            }
        }
        if (overlap_fail) continue;

        // Place word and save state
        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] == '.') {
                memo.push_back({p.pos[i], '.'});
                grid[p.pos[i]] = p.vals[i];
            }
        }

        // Update domains for future words based on this choice
        bool dead_end = false;
        vector<Mask> next_domains = current_domains;
        
        for (int n_w = w_idx + 1; n_w < (int)req_words.size(); ++n_w) {
            next_domains[n_w] &= conflicts[w_idx][p_idx][n_w];
            if (next_domains[n_w].none()) {
                dead_end = true;
                break;
            }
        }

        if (!dead_end) {
            domain_stack.push_back(next_domains);
            solve_required(w_idx + 1);
            domain_stack.pop_back();
        }

        // Backtrack
        for (auto& m : memo) {
            grid[m.first] = m.second;
        }
        
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

    string t, v;
    while (in >> t >> v) {
        if (t == "+") {
            req_words.push_back(v);
        } else {
            insert_forbidden(v);
        }
    }

    // Sort longest to shortest (helps prune search space faster)
    sort(req_words.begin(), req_words.end(), [](const string& a, const string& b) {
        return a.length() > b.length();
    });

    int n = req_words.size();
    choices.resize(n);
    vector<Mask> initial_domains(n);

    // Precalculate every placement for every word on an empty board
    for (int i = 0; i < n; ++i) {
        int len = req_words[i].length();
        for (int row = 0; row < height; row++) {
            for (int col = 0; col < width; col++) {
                for (int dir = 0; dir < 8; dir++) {
                    int end_row = row + dx[dir] * (len - 1);
                    int end_col = col + dy[dir] * (len - 1);
                    if (end_row >= 0 && end_row < height && end_col >= 0 && end_col < width) {
                        Placement p;
                        for (int k = 0; k < len; k++) {
                            p.pos.push_back((row + dx[dir] * k) * width + (col + dy[dir] * k));
                            p.vals.push_back(req_words[i][k]);
                        }
                        choices[i].push_back(p);
                        if (choices[i].size() <= MAX_P) {
                            initial_domains[i].set(choices[i].size() - 1);
                        }
                    }
                }
            }
        }
    }

    // OPTIMIZED: Allocate conflicts array only for actual placement counts
    conflicts = new Mask**[n];
    for (int i = 0; i < n; ++i) {
        int num_placements = min((int)choices[i].size(), MAX_P);
        conflicts[i] = new Mask*[num_placements];
        for (int p = 0; p < num_placements; ++p) {
            conflicts[i][p] = new Mask[n];
            for (int j = 0; j < n; ++j) {
                conflicts[i][p][j].set();
            }
        }
    }

    // Fill conflict matrix (mark which instances clash)
    for (int i = 0; i < n; ++i) {
        int i_placements = min((int)choices[i].size(), MAX_P);
        for (int p1 = 0; p1 < i_placements; ++p1) {
            for (int j = 0; j < n; ++j) {
                if (i == j) continue;
                int j_placements = min((int)choices[j].size(), MAX_P);
                for (int p2 = 0; p2 < j_placements; ++p2) {
                    bool conflicts_found = false;
                    for (size_t k1 = 0; k1 < choices[i][p1].pos.size() && !conflicts_found; ++k1) {
                        for (size_t k2 = 0; k2 < choices[j][p2].pos.size(); ++k2) {
                            if (choices[i][p1].pos[k1] == choices[j][p2].pos[k2] &&
                                choices[i][p1].vals[k1] != choices[j][p2].vals[k2]) {
                                conflicts[i][p1][j].reset(p2);
                                conflicts_found = true;
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    // Initialize domain stack with initial domains
    domain_stack.push_back(initial_domains);

    // Solve using optimized backtracking
    solve_required(0);

    // Output results
    if (unique_boards.empty()) {
        out << "No solutions found" << endl;
    } else if (mode == "one_solution") {
        out << "Board:" << endl;
        const string& s = *unique_boards.begin();
        for (int i = 0; i < height; ++i) {
            out << "  ";
            for (int j = 0; j < width; ++j) {
                out << s[i * width + j];
            }
            out << endl;
        }
    } else {
        out << unique_boards.size() << " solution(s)" << endl;
        for (const string& s : unique_boards) {
            out << "Board:" << endl;
            for (int i = 0; i < height; ++i) {
                out << "  ";
                for (int j = 0; j < width; ++j) {
                    out << s[i * width + j];
                }
                out << endl;
            }
        }
    }

    // Cleanup
    for (int i = 0; i < n; ++i) {
        int num_placements = min((int)choices[i].size(), MAX_P);
        for (int p = 0; p < num_placements; ++p) {
            delete[] conflicts[i][p];
        }
        delete[] conflicts[i];
    }
    delete[] conflicts;

    return 0;
}
