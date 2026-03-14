#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <cstring>
#include <bitset>
#include <set>

using namespace std;

// MAX_P: Maximum possible locations a single word can fit on the board.
// Mask: A bitset "checklist" to track which placements are still valid.
const int MAX_P = 1024;
typedef bitset<MAX_P> Mask;

struct Placement {
    vector<int> pos;
    string vals;
};

struct TrieNode {  //trie for forbidden words
    int children[26]; //indices of next letters in the trie
    bool is_end; //marks the end of a forbidden word
    TrieNode() { memset(children, -1, sizeof(children)); is_end = false; }
};
vector<TrieNode> trie;

//adds a forbidden word into the Trie.
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
    trie[curr].is_end = true; //mark that a forbidden word ends here
}

int width, height, total_cells;
char grid[2601];
string mode;
vector<string> req_words;
vector<vector<Placement>> choices;
set<string> unique_boards; // set automatically gets rid of duplicates
Mask*** conflicts = nullptr; //if word 1 is at x, word 2 can't be at y

int dx[] = {-1, -1, 0, 1, 1, 1, 0, -1};
int dy[] = {0, 1, 1, 1, 0, -1, -1, -1};

//checks if any direction form a word found in Trie
bool creates_forbidden(int row, int col) {
    for (int dir = 0; dir < 8; ++dir) {
        int curr = 0;
        for (int k = 0; ; ++k) {
            int new_row = row + dx[dir] * k, new_col = col + dy[dir] * k;
            //stop if off board or if cell is still empty
            if (new_row < 0 || new_row >= height || new_col < 0 || new_col >= width || grid[new_row * width + new_col] == '.') break;
            int v = grid[new_row * width + new_col] - 'a';
            if (trie[curr].children[v] == -1) break;
            curr = trie[curr].children[v];
            if (trie[curr].is_end) return true; //found full forbidden word
        }
    }
    return false;
}

//scans the entire board for forbidden words
bool final_safety_check() {
    for (int row = 0; row < height; ++row) {
        for (int col = 0; col < width; ++col) {
            if (creates_forbidden(row, col)) return true;
        }
    }
    return false;
}

//recursively tries filling empty '.' cells with 'a-z'.
void fill_remaining(int cell_idx, const vector<int>& empty_cells) {
    if (cell_idx == (int)empty_cells.size()) {
        if (!final_safety_check()) unique_boards.insert(string(grid, total_cells));
        return;
    }

    int pos = empty_cells[cell_idx];
    for (char c = 'a'; c <= 'z'; ++c) {
        grid[pos] = c;
        //only check the area just changed to save time
        if (!creates_forbidden(pos / width, pos % width)) {
            fill_remaining(cell_idx + 1, empty_cells);
            if (mode == "one_solution" && !unique_boards.empty()) return;
        }
        grid[pos] = '.'; //backtrack
    }
}

//places required words using backtracking
void solve_required(int w_idx, vector<Mask> domains) {
    if (w_idx == (int)req_words.size()) {
        vector<int> empty_cells;
        for (int i = 0; i < total_cells; ++i) if (grid[i] == '.') empty_cells.push_back(i);
        
        if (empty_cells.empty()) {
            if (!final_safety_check()) unique_boards.insert(string(grid, total_cells));
        } else {
            fill_remaining(0, empty_cells);
        }
        return;
    }

    Mask active = domains[w_idx]; 
    for (int p_idx = 0; p_idx < (int)choices[w_idx].size(); ++p_idx) {
        if (!active.test(p_idx)) continue; //skip clashing spots

        const auto& p = choices[w_idx][p_idx];
        bool overlap_fail = false;
        vector<pair<int, char>> memo;

        //verify word can fit with existing letters
        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] != '.' && grid[p.pos[i]] != p.vals[i]) { overlap_fail = true; break; }
        }
        if (overlap_fail) continue;

        //place word
        for (size_t i = 0; i < p.pos.size(); ++i) {
            if (grid[p.pos[i]] == '.') {
                memo.push_back({p.pos[i], '.'});
                grid[p.pos[i]] = p.vals[i];
            }
        }

        //update checklists for all future words based on this choice
        vector<Mask> next_domains = domains;
        bool dead_end = false;
        for (int n_w = w_idx + 1; n_w < (int)req_words.size(); ++n_w) {
            next_domains[n_w] &= conflicts[w_idx][p_idx][n_w];
            if (next_domains[n_w].none()) { dead_end = true; break; }
        }

        if (!dead_end) solve_required(w_idx + 1, next_domains);

        //backtrack
        for (auto& m : memo) grid[m.first] = m.second;
        if (mode == "one_solution" && !unique_boards.empty()) return;
    }
}

int main(int argc, char* argv[]) {
    if (argc < 4) return 1;
    ios::sync_with_stdio(0); cin.tie(0); //improves speed
    ifstream in(argv[1]); ofstream out(argv[2]); mode = argv[3];
    
    if (!(in >> width >> height)) return 0;
    total_cells = width * height;
    memset(grid, '.', total_cells);
    trie.push_back(TrieNode()); //initialize root of trie

    string t, v;
    while (in >> t >> v) {
        if (t == "+") req_words.push_back(v);
        else {
            insert_forbidden(v); 
            //add reversed too
            string r = v; reverse(r.begin(), r.end());
            if (r != v) insert_forbidden(r); 
        }
    }

    //sort longest to shortest
    sort(req_words.begin(), req_words.end(), [](const string& a, const string& b){
        return a.length() > b.length();
    });

    int n = req_words.size();
    choices.resize(n);
    vector<Mask> initial_domains(n);

    //precalculate every placement for every word on an empty board
    for (int i = 0; i < n; ++i) {
        int len = req_words[i].length();
        for (int row=0; row<height; row++) for (int col=0; col<width; col++) for (int dir=0; dir<8; dir++) {
            int end_row = row + dx[dir]*(len-1), end_col = col + dy[dir]*(len-1);
            if (end_row >= 0 && end_row < height && end_col >= 0 && end_col < width) {
                Placement p;
                for (int k=0; k<len; k++) {
                    p.pos.push_back((row+dx[dir]*k)*width + (col+dy[dir]*k));
                    p.vals.push_back(req_words[i][k]);
                }
                choices[i].push_back(p);
                if(choices[i].size() <= MAX_P) initial_domains[i].set(choices[i].size()-1);
            }
        }
    }

    //conflict matrix
    conflicts = new Mask**[n];
    for(int i=0; i<n; ++i) {
        conflicts[i] = new Mask*[MAX_P];
        for(int p=0; p<MAX_P; ++p) {
            conflicts[i][p] = new Mask[n];
            for(int j=0; j<n; ++j) conflicts[i][p][j].set();
        }
    }

    //fill conflict matrix (mark which instances clash - use same cell but have diff letter)
    for (int i = 0; i < n; ++i) {
        for (int p1 = 0; p1 < (int)choices[i].size() && p1 < MAX_P; ++p1) {
            for (int j = 0; j < n; ++j) {
                if (i == j) continue;
                for (int p2 = 0; p2 < (int)choices[j].size() && p2 < MAX_P; ++p2) {
                    for (size_t k1=0; k1<choices[i][p1].pos.size(); ++k1) {
                        for (size_t k2=0; k2<choices[j][p2].pos.size(); ++k2) {
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
    }
    else {

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