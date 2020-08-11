#include <vector>
#include <unordered_set>
#include <fstream>
#include <string>
#include <iostream>
#include <sstream>
#include <algorithm>
#include <iterator>
#include <unordered_map>
#include <ctime>
#include <cstdlib>

using namespace std;

class ResolutionProver {
private:
	vector<unordered_set<int>> knownClauses;
	vector<unordered_set<int>> newClauses;
	unordered_set<int> variables;

	void printClauses() {
		cout << "size\n";
		cout << knownClauses.size();
		cout << "First Ten Clauses : \n";
		for (int i = 0; i < knownClauses.size(); i++) {
			cout << "[";
			for (int var : knownClauses[i]){
				cout << var << ", ";
			}
			cout << "]\n";
		}
	}

	bool resolveClauses(unordered_set<int>& clause1, unordered_set<int>& clause2, unordered_set<int>& resolvent) {
		vector<unordered_set<int>> clauses;
		int complementaryVar = 0;
		for (int var1 : clause1) {
			if (clause2.find(-var1) != clause2.end()) {	//complementary pair found
				if (complementaryVar == 0) {
					complementaryVar = var1;
				}
				else {
					//multiple complementary literals found no valid results
					return false;
				}
			}
		}
		if (complementaryVar != 0) {
			set_union(begin(clause1), end(clause1),
				begin(clause2), end(clause2),
				inserter(resolvent, std::begin(resolvent)));

			resolvent.erase(complementaryVar);
			resolvent.erase(-complementaryVar);
			
			return true;
		}
		return false;
	}

	bool equals(unordered_set<int>& clause1, unordered_set<int>& clause2) { //return true if they contain the same elements
		if (clause1.size() == clause2.size()) {
			for (int var : clause1) {
				if (clause2.find(var) == clause2.end()) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

public:
	ResolutionProver() {
		knownClauses.clear();
		newClauses.clear();
	}

	bool prove() {
		while (true) {
			//resolve each pair
			newClauses.clear();
			for (int i = 0; i < knownClauses.size(); ++i) {
				for (int k = i + 1; k < knownClauses.size(); ++k) {
					unordered_set<int> resolvent;
					bool results = resolveClauses(knownClauses[i], knownClauses[k], resolvent);
					if (results) {
						if (resolvent.empty()) {
							cout << "query is entailed\n";
							return true;
						}
						newClauses.push_back(resolvent);
					}
				}
			}
			bool isSubset = true;
			for (size_t n = 0; n < newClauses.size(); ++n) {
				bool goodClause = true;
				for (size_t k = 0; k < knownClauses.size(); ++k) {
					if (equals(knownClauses[k], newClauses[n])) { //is duplicate ignore
						goodClause = false;
						break;
					}
				}
				if (goodClause) {
					isSubset = false;
					knownClauses.push_back(newClauses[n]);
				}
			}
			if (isSubset) {
				cout << "query is not entailed\n";
				return false;
			}
		}
	}

	bool loadFile(string path) {
		knownClauses.clear();
		ifstream file(path);
		string line;
		bool firstLine = true;
		int num_variables = 0;
		int num_clauses = 0;
		while (getline(file, line)) {
			//https://stackoverflow.com/questions/236129/how-do-i-iterate-over-the-words-of-a-string split by space
			istringstream iss(line);
			vector<string> tokens{ istream_iterator<string>{iss},
				  istream_iterator<string>{} };

			if (tokens[0] == "c") {
				//is comment line ignore
				continue;
			}
			if (firstLine) {
				if (tokens[0] == "p" && tokens[1] == "cnf") {
					num_variables = stoi(tokens[2]);
					num_clauses = stoi(tokens[3]);
					firstLine = false;
				}
				else {
					//invalid file
					return false;
				}
			}
			else {
				unordered_set<int> clause;
				for (string var : tokens) {
					int variable = stoi(var);
					if (variable != 0) {
						clause.insert(variable);
						variables.insert(abs(variable));
					}
				}
				knownClauses.push_back(clause);
			}
		}
		return true;
	}

	void loadQuery(int argc, char** argv) {
		for (int i = 2; i < argc; i++) {
			unordered_set<int> one;
			one.insert(-atoi(argv[i]));
			knownClauses.push_back(one);
		}
	}

};

int main(int argc, char** argv) {
	cout << "Resolution Prover Program\n";
	ResolutionProver RP;
	if (argc > 2) {
		RP.loadFile(argv[1]);
		RP.loadQuery(argc, argv);
		RP.prove();
	}
	else {
		cout << "Please provide path to file and some assignment!\n";
	}
}