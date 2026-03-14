Skip to main content
1
#include <iostream>
2
#include <vector>
3
#include <string>
4
#include <algorithm>
5
#include <fstream>
6
#include <cstring>
7
​
8
using namespace std;
9
​
10
//static constants for speed
11
const int MAX_NODES = 300000; 
12
const int MAX_DIM = 2601; 
13
​
14
int trie_flat[MAX_NODES * 26]; //
15
bool trie_end[MAX_NODES];
16
int trie_count = 1; //trie_count starts at 1 because 0 is the root node and is already initialized
17
char grid[MAX_DIM];
18
int width, height, total_cells;
19
int max_f_len = 0; //max length of forbidden words to optimize trie checks
20
string mode; //"one_solution" or "all_solutions"
21
​
22
int dx[] = {-1, -1, 0, 1, 1, 1, 0, -1}; //row movement 
23
int dy[] = {0, 1, 1, 1, 0, -1, -1, -1}; //col movement
24
//left, right, down, up, down-right, up-left, down-left, up-right
25
​
26
char alpha[] = "etaoinshrdlcumwfgypbvkjxqz"; //letter frequency order for faster backtracking
27
//tries more common letters first to find solutions faster
28
//taken from https://www.sttmedia.com/characterfrequency-english
29
​
30
struct Placement { int row, col, dir; };
31
vector<string> required_words; //(+)
32
//stores all possible board positions for each required word
33
vector<vector<Placement>> word_placements; 
34
vector<string> solutions; //switched to vector for speed/memory
35
​
36
//inserts forbidden word into trie
37
void insert_forbidden(const string& s) {
38
    if ((int)s.length() > max_f_len) max_f_len = (int)s.length();
39
    int curr = 0;
40
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
96
}
97
​
98
//fill remaining empty cells with backtracking
99
void fill_grid(int pos) {
100
    if (mode == "one_solution" && !solutions.empty()) return;
101
    if (pos == total_cells) {
102
        solutions.push_back(string(grid, total_cells));
103
        return;
104
    }
105
    if (grid[pos] != '.') { //cell already has a letter
106
        fill_grid(pos + 1); //move to next cell
107
    } else {
108
        if (total_cells - pos > 10 && (pos % 2 == 0) && has_future_deadspot(pos)) return;
109
​
110
        int row = pos / width, col = pos % width;
111
        for (int i = 0; i < 26; ++i) { //try all letters in frequeny order
112
            grid[pos] = alpha[i];
113
            if (is_safe(row, col)) fill_grid(pos + 1);
114
            if (mode == "one_solution" && !solutions.empty()) return;
115
        }
116
        grid[pos] = '.'; //backtrack
117
    }
118
}
119
​
120
//place required words into the grid recursively
121
void solve_required(int idx) {
122
    if (mode == "one_solution" && !solutions.empty()) return;
123
    if (idx == (int)required_words.size()) {
124
        fill_grid(0); //all required words placed, fill remaining grid
125
        return;
126
    }
127
​
128
    const string& w = required_words[idx];
129
    int len = w.length();
130
    int changed[MAX_DIM];
131
​
132
    //iterate only through pre-validated positions
133
    for (vector<Placement>::const_iterator it = word_placements[idx].begin(); it != word_placements[idx].end(); ++it){
134
        const Placement& p = *it;
135
        bool can_place = true;
136
        //check if word can be placed here
137
        for (int i = 0; i < len; ++i) {
138
            char ex = grid[(p.row + dx[p.dir] * i) * width + (p.col + dy[p.dir] * i)];
139
            //ex is esisting char in grid
140
            if (ex != '.' && ex != w[i]) { can_place = false; break; }
141
        }
142
​
143
        if (can_place) {
144
            //place the word
145
            int count = 0;
146
            bool safe = true;
147
            for (int i = 0; i < len; ++i) {
148
                int current_row = p.row + dx[p.dir] * i, current_col = p.col + dy[p.dir] * i;
149
                int idx_1d = current_row * width + current_col;
150
                if (grid[idx_1d] == '.') {
151
                    grid[idx_1d] = w[i];
152
                    changed[count++] = idx_1d;
153
                    //verify placement against forbidden words
154
                    if (!is_safe(current_row, current_col)) { safe = false; break; }
155
                }
156
            }
157
            if (safe) solve_required(idx + 1);
158
            for (int i = 0; i < count; ++i) 
159
                grid[changed[i]] = '.';
160
        }
161
    }
162
}
163
​
164
int main(int argc, char* argv[]) {
165
    ios_base::sync_with_stdio(false); cin.tie(NULL);//speeds up
166
    //https://medium.com/@harshks.mit/turbocharge-your-c-input-output-performance-understanding-ios-base-sync-with-stdio-false-and-d867d072e079
167
    if (argc < 4) return 1;
168
    ifstream infile(argv[1]);
169
    ofstream outfile(argv[2]);
170
    mode = argv[3];
171
    
172
    infile >> width >> height;
173
    total_cells = width * height;
174
​
175
    // instead of for (int i = 0; i < total_cells; ++i) grid[i] = '.';
176
    memset(grid, '.', total_cells);
177
​
178
    string type, val;
179
    while (infile >> type >> val) {
180
        if (type == "+") required_words.push_back(val);
181
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
221
    }
222
​
223
    if (mode == "one_solution") {
224
​
225
        outfile << "Board:" << endl;
226
        const string& s = *solutions.begin();
227
        for (int i = 0; i < height; ++i) {
228
            outfile << "  ";
229
            for (int j = 0; j < width; ++j) outfile << s[i * width + j];
230
            outfile << endl;
231
        }
232
    }
233
    else {
234
​
235
        outfile << solutions.size() << " solution(s)" << endl;
236
        for (const string& s : solutions) {
237
            outfile << "Board:" << endl;
238
            for (int i = 0; i < height; ++i) {
239
                outfile << "  ";
240
                for (int j = 0; j < width; ++j) outfile << s[i * width + j];
241
                outfile << endl;
242
            }
243
        }
244
    }    
245
    return 0;
246
​
247
}
