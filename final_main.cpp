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
41
        int idx = c - 'a';
42
        if (!trie_flat[curr * 26 + idx]) trie_flat[curr * 26 + idx] = trie_count++;
43
        curr = trie_flat[curr * 26 + idx];
44
    }
45
    trie_end[curr] = true;
46
}
47
​
48
//inline for maximum speed since this is called very often in the backtracking
49
//it reduces function-call overhead by telling compiler to replace calls to this function
50
// with the actual code of the function
51
//check if placing a letter at (row, col) would create a forbidden word
52
inline bool is_safe(int row, int col) {
53
    for (int dir = 0; dir < 8; ++dir) {
54
        //only checks windows that overlap (row, col). 
55
        for (int offset = 0; offset < max_f_len; ++offset) {
56
            int start_row = row - dx[dir] * offset, start_col = col - dy[dir] * offset;
57
            
58
            if (start_row < 0 || start_row >= height || start_col < 0 || start_col >= width) continue;
59
​
60
            int node = 0;
61
            for (int i = 0; i < max_f_len; ++i) {
62
                int current_row = start_row + dx[dir] * i;
63
                int current_col = start_col + dy[dir] * i;
64
                
65
                if (current_row < 0 || current_row >= height || current_col < 0 || current_col >= width) break;
66
                
67
                char val = grid[current_row * width + current_col];
68
                if (val == '.') break; 
69
​
70
                node = trie_flat[node * 26 + (val - 'a')];
71
                if (!node) break; 
72
                
73
                if (trie_end[node] && i >= offset) return false;
74
            }
75
        }
76
    }
77
    return true;
78
}
79
​
80
//forward check, that every empty cell still has at least one valid letter
81
bool has_future_deadspot(int start_pos) { 
82
    //only check the very next empty cell. 
83
    for (int p = start_pos + 1; p < total_cells; ++p) {
84
        if (grid[p] == '.') {
85
            int row = p / width, col = p % width;
86
            bool possible = false;
87
            for (int i = 0; i < 26; ++i) {
88
                grid[p] = alpha[i];
89
                if (is_safe(row, col)) { possible = true; grid[p] = '.'; break; }
90
            }
91
            grid[p] = '.';
92
            return !possible; //can't be filled
93
        }
94
    }
95
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
182
            insert_forbidden(val);
183
            string rev = val; reverse(rev.begin(), rev.end());
184
            insert_forbidden(rev);
185
        }
186
    }
187
​
188
    //sort by least options
189
    vector<pair<int, int>> meta;
190
    for (int i = 0; i < (int)required_words.size(); ++i) {
191
        vector<Placement> opts;
192
        int len = required_words[i].length();
193
        for (int row = 0; row < height; ++row) {
194
            for (int col = 0; col < width; ++col) {
195
                for (int dir = 0; dir < 8; ++dir) {
196
                    if (row+dx[dir]*(len-1)>=0 && row+dx[dir]*(len-1)<height && col+dy[dir]*(len-1)>=0 && col+dy[dir]*(len-1)<width)
197
                        opts.push_back({row, col, dir});
198
                }
199
            }
200
        }
201
        word_placements.push_back(opts);
202
        meta.push_back({(int)opts.size(), i});
203
    }
204
    sort(meta.begin(), meta.end());
205
    vector<string> sw; vector<vector<Placement>> sp;
206
    for (vector<pair<int, int> >::iterator it = meta.begin(); it != meta.end(); ++it) {
207
        sw.push_back(required_words[it->second]);
208
        sp.push_back(word_placements[it->second]);
209
    }
210
    required_words = sw; word_placements = sp;
211
​
212
    solve_required(0);
213
​
214
    //remove duplicates since solutions are stored in vector for speed/memory
215
    sort(solutions.begin(), solutions.end());
216
    solutions.erase(unique(solutions.begin(), solutions.end()), solutions.end());
217
​
218
    if (solutions.empty()) {
219
        outfile << "No solutions found" << endl;
220
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
