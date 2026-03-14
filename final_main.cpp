#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <fstream>
#include <cstring>

using namespace std;

//static constants for speed
const int MAX_NODES = 300000; 
const int MAX_DIM = 2601; 

int trie_flat[MAX_NODES * 26]; //
bool trie_end[MAX_NODES];
int trie_count = 1; //trie_count starts at 1 because 0 is the root node and is already initialized
char grid[MAX_DIM];
int width, height, total_cells;
int max_f_len = 0; //max length of forbidden words to optimize trie checks
string mode; //"one_solution" or "all_solutions"

int dx[] = {-1, -1, 0, 1, 1, 1, 0, -1}; //row movement 
int dy[] = {0, 1, 1, 1, 0, -1, -1, -1}; //col movement
//left, right, down, up, down-right, up-left, down-left, up-right

char alpha[] = "etaoinshrdlcumwfgypbvkjxqz"; //letter frequency order for faster backtracking
//tries more common letters first to find solutions faster
//taken from https://www.sttmedia.com/characterfrequency-english

struct Placement { int row, col, dir; };
vector<string> required_words; //(+)
//stores all possible board positions for each required word
vector<vector<Placement>> word_placements; 
vector<string> solutions; //switched to vector for speed/memory

//inserts forbidden word into trie
void insert_forbidden(const string& s) {
    if ((int)s.length() > max_f_len) max_f_len = (int)s.length();
    int curr = 0;
    for (char c : s) {
        int idx = c - 'a';
        if (!trie_flat[curr * 26 + idx]) trie_flat[curr * 26 + idx] = trie_count++;
        curr = trie_flat[curr * 26 + idx];
    }
    trie_end[curr] = true;
}

//inline for maximum speed since this is called very often in the backtracking
//it reduces function-call overhead by telling compiler to replace calls to this function
// with the actual code of the function
//check if placing a letter at (row, col) would create a forbidden word
inline bool is_safe(int row, int col) {
    for (int dir = 0; dir < 8; ++dir) {
        for (int offset = 0; offset < max_f_len; ++offset) {
            int start_row = row - dx[dir] * offset;
            int start_col = col - dy[dir] * offset;
            
            if (start_row < 0 || start_row >= height || start_col < 0 || start_col >= width) continue;

            int node = 0;
            bool valid_window = true;
            for (int i = 0; i < max_f_len; ++i) {
                int current_row = start_row + dx[dir] * i;
                int current_col = start_col + dy[dir] * i;
                
                if (current_row < 0 || current_row >= height || current_col < 0 || current_col >= width) break;
                
                char ch = grid[current_row * width + current_col];
                if (ch == '.') break;
                
                int idx = ch - 'a';
                if (!trie_flat[node * 26 + idx]) {
                    valid_window = false;
                    break;
                }
                node = trie_flat[node * 26 + idx];
                
                if (trie_end[node]) return false; // Found forbidden word early
            }
        }
    }
    return true;
}

//forward check, that every empty cell still has at least one valid letter
bool has_future_deadspot(int start_pos) { 
    //only check the very next empty cell. 
    for (int p = start_pos + 1; p < total_cells; ++p) {
        if (grid[p] == '.') {
            int row = p / width, col = p % width;
            bool possible = false;
            for (int i = 0; i < 26; ++i) {
                grid[p] = alpha[i];
                if (is_safe(row, col)) { possible = true; grid[p] = '.'; break; }
            }
            grid[p] = '.';
            return !possible; //can't be filled
        }
    }
    return false;
}

//fill remaining empty cells with backtracking
void fill_grid(int pos) {
    if (mode == "one_solution" && !solutions.empty()) return;
    if (pos == total_cells) {
        solutions.push_back(string(grid, total_cells));
        return;
    }
    if (grid[pos] != '.') { //cell already has a letter
        fill_grid(pos + 1); //move to next cell
    } else {
        if (total_cells - pos > 10 && (pos % 2 == 0) && has_future_deadspot(pos)) return;

        int row = pos / width, col = pos % width;
        for (int i = 0; i < 26; ++i) { //try all letters in frequeny order
            grid[pos] = alpha[i];
            if (is_safe(row, col)) fill_grid(pos + 1);
            if (mode == "one_solution" && !solutions.empty()) return;
        }
        grid[pos] = '.'; //backtrack
    }
}

//place required words into the grid recursively
void solve_required(int idx) {
    if (mode == "one_solution" && !solutions.empty()) return;
    if (idx == (int)required_words.size()) {
        fill_grid(0); //all required words placed, fill remaining grid
        return;
    }

    const string& w = required_words[idx];
    int len = w.length();
    int changed[MAX_DIM];

    //iterate only through pre-validated positions
    for (vector<Placement>::const_iterator it = word_placements[idx].begin(); it != word_placements[idx].end(); ++it){
        const Placement& p = *it;
        bool can_place = true;
        //check if word can be placed here
        for (int i = 0; i < len; ++i) {
            char ex = grid[(p.row + dx[p.dir] * i) * width + (p.col + dy[p.dir] * i)];
            //ex is esisting char in grid
            if (ex != '.' && ex != w[i]) { can_place = false; break; }
        }

        if (can_place) {
            //place the word
            int count = 0;
            bool safe = true;
            for (int i = 0; i < len; ++i) {
                int current_row = p.row + dx[p.dir] * i, current_col = p.col + dy[p.dir] * i;
                int idx_1d = current_row * width + current_col;
                if (grid[idx_1d] == '.') {
                    grid[idx_1d] = w[i];
                    changed[count++] = idx_1d;
                    //verify placement against forbidden words
                    if (!is_safe(current_row, current_col)) { safe = false; break; }
                }
            }
            if (safe) solve_required(idx + 1);
            for (int i = 0; i < count; ++i) 
                grid[changed[i]] = '.';
        }
    }
}

int main(int argc, char* argv[]) {
    ios_base::sync_with_stdio(false); cin.tie(NULL);//speeds up
    //https://medium.com/@harshks.mit/turbocharge-your-c-input-output-performance-understanding-ios-base-sync-with-stdio-false-and-d867d072e079
    if (argc < 4) return 1;
    ifstream infile(argv[1]);
    ofstream outfile(argv[2]);
    mode = argv[3];
    
    infile >> width >> height;
    total_cells = width * height;

    // instead of for (int i = 0; i < total_cells; ++i) grid[i] = '.';
    memset(grid, '.', total_cells);

    string type, val;
    while (infile >> type >> val) {
        if (type == "+") required_words.push_back(val);
        else {
            insert_forbidden(val);
            string rev = val; reverse(rev.begin(), rev.end());
            insert_forbidden(rev);
        }
    }

    //sort by least options
    vector<pair<int, int>> meta;
    for (int i = 0; i < (int)required_words.size(); ++i) {
        vector<Placement> opts;
        int len = required_words[i].length();
        for (int row = 0; row < height; ++row) {
            for (int col = 0; col < width; ++col) {
                for (int dir = 0; dir < 8; ++dir) {
                    if (row+dx[dir]*(len-1)>=0 && row+dx[dir]*(len-1)<height && col+dy[dir]*(len-1)>=0 && col+dy[dir]*(len-1)<width)
                        opts.push_back({row, col, dir});
                }
            }
        }
        word_placements.push_back(opts);
        meta.push_back({(int)opts.size(), i});
    }
    sort(meta.begin(), meta.end());
    vector<string> sw; vector<vector<Placement>> sp;
    for (vector<pair<int, int> >::iterator it = meta.begin(); it != meta.end(); ++it) {
        sw.push_back(required_words[it->second]);
        sp.push_back(word_placements[it->second]);
    }
    required_words = sw; word_placements = sp;

    solve_required(0);

    //remove duplicates since solutions are stored in vector for speed/memory
    sort(solutions.begin(), solutions.end());
    solutions.erase(unique(solutions.begin(), solutions.end()), solutions.end());

    if (solutions.empty()) {
        outfile << "No solutions found" << endl;
        return 0;
    }

    if (mode == "one_solution") {

        outfile << "Board:" << endl;
        const string& s = *solutions.begin();
        for (int i = 0; i < height; ++i) {
            outfile << "  ";
            for (int j = 0; j < width; ++j) outfile << s[i * width + j];
            outfile << endl;
        }
    }
    else {

        outfile << solutions.size() << " solution(s)" << endl;
        for (const string& s : solutions) {
            outfile << "Board:" << endl;
            for (int i = 0; i < height; ++i) {
                outfile << "  ";
                for (int j = 0; j < width; ++j) outfile << s[i * width + j];
                outfile << endl;
            }
        }
    }    
    return 0;

}
