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

unordered_set<string> forbidden_words;

void insert_forbidden(const string& s) {
    forbidden_words.insert(s);
    string r = s;
    reverse(r.begin(), r.end());
    if (r != s) {
        forbidden_words.insert(r);
    }
}

int width, height, total_cells;
char grid[2601];
string mode;
vector<string> req_words;
vector<vector<Placement>> choices;
unordered_set<string> unique_boards;

// FIXED: Only allocate for actual placements, not MAX_P
vector<vector<vector<Mask>>> conflicts;

int dx[] = {-1, -1, 0, 1, 1, 1, 0, -1};
int dy[] = {0, 1, 1, 1, 0, -1, -1, -1};

bool creates_forbidden(int row, int col) {
    for (int dir = 0; dir < 8; ++dir) {
        string word = "";
        for (int k = 0; ; ++k) {
            int new_row = row + dx[dir] * k;
            int new_col = col + dy[dir] * k;
            
            if (new_row < 0 || new_row >= height || new_col < 0 || new_col >= width || 
                grid[new_row * width + new_col] == '.') {
                break;
            }
            
            word += grid[new_row * width + new_col];
            
            if (word.length() >= 2 && forbidden_words.count(word) > 0) {
                return true;
            }
        }
    }
    return false;
}

bool final_safety_check() {
    for (int row = 0; row < height; ++row) {
        for (int col = 0; col < width; ++col) {
            if (creates_forbidden(row, col)) return true;
        }
    }
    return false;
}

void fill_remaining(int cell_idx, const vector<int>& empty_cells) {
    if (cell_idx == (int)empty_cells.size()) {
        if (!final_safety_check()) {
            unique_boards.insert(string(grid, total_cells));
        }
        return;
    }

    int pos = empty_cells[cell_idx];
    for (char c = 'a'; c <= 'z'; ++c) {
        grid[pos] = c;
        if (!creates_forbidden(pos / width, pos % width)) {
            fill_remaining(cell_idx + 1, empty_cells);
            if (mode == "one_solution" && !unique_boards.empty()) return;
        }
        grid[pos] = '.';
    }
}

void solve_required(int w_idx, vector<Mask> domains) {
    if (w_idx == (int)req_words.size()) {
        vector<int> empty_cells;
        for (int i = 0; i < total_cells; ++i) if (grid[i] == '.') empty_cells.push_back(i);
        
        if (empty_cells.empty()) {
            if (!final_safety_check()) {
                unique_boards.insert(string(grid, total_cells));
            }
        } else {
            fill_remaining(0, empty_cells);
        }
        return;
    }

    Mask active = domains[w_idx];
    for (int p_idx = 0; p_idx < (int)choices[w_idx].size(); ++p_idx) {
        if (!active.test(p_idx)) continue;

        const auto& p = choices[w_idx][p_idx];
        bool overlap_fail = false;
        vector<pair<int, char>> memo;

        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] != '.' && grid[p.pos[i]] != p.vals[i]) {
                overlap_fail = true;
                break;
            }
        }
        if (overlap_fail) continue;

        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] == '.') {
                memo.push_back({p.pos[i], '.'});
                grid[p.pos[i]] = p.vals[i];
            }
        }

        vector<Mask> next_domains = domains;
        bool dead_end = false;
        for (int n_w = w_idx + 1; n_w < (int)req_words.size(); ++n_w) {
            // FIXED: Safe access to conflicts vector
            if (p_idx < (int)conflicts[w_idx].size()) {
                next_domains[n_w] &= conflicts[w_idx][p_idx][n_w];
                if (next_domains[n_w].none()) {
                    dead_end = true;
                    break;
                }
            }
        }

        if (!dead_end) solve_required(w_idx + 1, next_domains);

        for (auto& m : memo) grid[m.first] = m.second;
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

    sort(req_words.begin(), req_words.end(), [](const string& a, const string& b) {
        return a.length() > b.length();
    });

    int n = req_words.size();
    choices.resize(n);
    vector<Mask> initial_domains(n);

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

    // FIXED: Initialize conflicts as vector<vector<vector<Mask>>>
    // Only allocate for actual placements
    conflicts.resize(n);
    for (int i = 0; i < n; ++i) {
        int num_placements = min((int)choices[i].size(), MAX_P);
        conflicts[i].resize(num_placements);
        for (int p = 0; p < num_placements; ++p) {
            conflicts[i][p].resize(n);
            for (int j = 0; j < n; ++j) {
                conflicts[i][p][j].set();
            }
        }
    }

    // Fill conflict matrix
    for (int i = 0; i < n; ++i) {
        for (int p1 = 0; p1 < (int)choices[i].size() && p1 < MAX_P; ++p1) {
            for (int j = 0; j < n; ++j) {
                if (i == j) continue;
                for (int p2 = 0; p2 < (int)choices[j].size() && p2 < MAX_P; ++p2) {
                    for (size_t k1 = 0; k1 < choices[i][p1].pos.size(); ++k1) {
                        for (size_t k2 = 0; k2 < choices[j][p2].pos.size(); ++k2) {
                            if (choices[i][p1].pos[k1] == choices[j][p2].pos[k2] &&
                                choices[i][p1].vals[k1] != choices[j][p2].vals[k2]) {
                                conflicts[i][p1][j].reset(p2);
                                goto next_p2;
                            }
                        }
                    }
                    next_p2:;
                }
            }
        }
    }

    solve_required(0, initial_domains);

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
