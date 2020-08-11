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

class WalkSat {
private:
	vector<vector<int>> clauses;
	vector<vector<int>> unsat;
	unordered_set<int> variables;
	unordered_map<int, bool> assignment;
	bool validAssignment;
	unordered_map<int, vector<int>> var2ClauseIndices;
	vector<bool> clauseStates;

	void printAssignment() {
		vector<int> printList;
		for (int var : variables) {
			if (assignment[var]) {
				printList.push_back(var);
			}
		}
		sort(printList.begin(), printList.end());
		cout << "Assignment : \n";
		cout << "[";
		for (int i = 0; i < printList.size(); i++) {
			cout << printList.at(i) << ", ";
		}
		cout << "]\n";
	}

	void printClauses() {
		cout << "size\n";
		cout << clauses.size();
		cout << "First Five Clauses : \n";
		for (int i = 0; i < 5; i++) {
			for (int n = 0; n < clauses.at(i).size(); n++) {
				cout << clauses.at(i).at(n) << ", ";
			}
			cout << "\n";
		}
	}

	void printVariables() {
		cout << "size\n";
		cout << variables.size();
		cout << "First Five Clauses : \n";
		for (int var : variables) {
			cout << var << ", ";
		}
	}

	bool clauseSatisfied(vector<int>& clause) {
		for (size_t i = 0; i < clause.size(); ++i) {
			int var = clause[i];
			if (var > 0) {
				if (assignment[abs(var)]) {
					return true;
				}
			}
			else if (!assignment[abs(var)]) {
				return true;
			}
		}
		return false;
	}

	int flipEffect(int var) {
		int effect = 0;
		for (int index : var2ClauseIndices[var]) {	//only look at clauses that contain the variable changed
			if (clauseStates[index]) {
				assignment[var] = !assignment[var];
				if (!clauseSatisfied(clauses[index])) {
					effect--;
				}
				assignment[var] = !assignment[var];
			}
			else {	//clause is false only if all variables in it are wrong, thus fliping one must make the whole statement true
				effect++;
			}
		}
		return effect;
	}

	int bestVariable(vector<int>& clause) {
		int max = -clauses.size();
		int bestVar = 0;
		for (int var : clause) {
			int effect = flipEffect(abs(var));
			if (effect > max) {
				bestVar = abs(var);
				max = effect;
			}
		}
		return bestVar;
	}

	void findUnsatisifiedClauses() {
		unsat.clear();
		for (size_t i = 0; i < clauses.size(); ++i) {
			if (!clauseStates[i]) {
				unsat.push_back(clauses[i]);
			}
		}
	}

	void constructClauseStates() {
		clauseStates.clear();
		for (size_t i = 0; i < clauses.size(); ++i) {
			clauseStates.push_back(clauseSatisfied(clauses[i]));
		}
	}

	void flipVariableAssignment(int var) {
		assignment[var] = !assignment[var];
		for (int index : var2ClauseIndices[var]) {	//only look at clauses that contain the variable changed
			if (clauseStates[index]) {
				clauseStates[index] = clauseSatisfied(clauses[index]);
			}
			else {	//clause is false only if all variables in it are wrong, thus fliping one must make the whole statement true
				clauseStates[index] = true;
			}
		}
	}


public:
	WalkSat() {
		validAssignment = false;
	}

	bool solve(float probability, int max) {
		constructClauseStates();
		for (int z = 0; z < max; z++) {
			findUnsatisifiedClauses();
			if (unsat.empty()) {
				//valid assignment found
				validAssignment = true;
				return true;
			}
			vector<int>& randUnsatClause = unsat.at(rand() % (unsat.size()));
			//https://stackoverflow.com/questions/686353/random-float-number-generation random float
			float r2 = static_cast <float> (rand()) / (static_cast <float> (RAND_MAX));
			if (r2 < probability) {
				//choose random variable in assignment and flip it
				int randVar = abs(randUnsatClause.at(rand() % (randUnsatClause.size())));
				flipVariableAssignment(randVar);
			}
			else {
				int bestVar = bestVariable(randUnsatClause);
				flipVariableAssignment(bestVar);
			}
		}
		//could not find valid assignment
		validAssignment = false;
		return false;
	}

	bool loadFile(string path) {
		ifstream file(path);
		string line;
		bool firstLine = true;
		int num_variables = 0;
		int num_clauses = 0;
		unordered_set<int> positivePure;
		unordered_set<int> negativePure;
		unordered_set<int> notPure;
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
				vector<int> clause;
				for (string var : tokens) {
					int variable = stoi(var);
					if (variable != 0) {
						clause.push_back(variable);
						variables.insert(abs(variable));
						if (notPure.find(abs(variable)) == notPure.end()) { //not in notPure
							if (variable > 0) {
								if (negativePure.find(abs(variable)) != negativePure.end()) {
									negativePure.erase(abs(variable));
									notPure.insert(abs(variable));
								}
								else {
									positivePure.insert(abs(variable));
								}
							}
							else { //negative var
								if (positivePure.find(abs(variable)) != positivePure.end()) {
									positivePure.erase(abs(variable));
									notPure.insert(abs(variable));
								}
								else {
									negativePure.insert(abs(variable));
								}
							}
						}
					}
				}
				clauses.push_back(clause);
			}
		}

		clauses.erase(
			remove_if(clauses.begin(), clauses.end(),
				[notPure](const vector<int>& clause) {
					for (int var : clause) {
						if (notPure.find(abs(var)) == notPure.end()) { //if any var in the clause are pure (not notPure) delete the clause
							return true;
						}
					}
					return false;
				}),
			clauses.end());
		//start with random assignment (better results)
		srand(time(0));
		for (int var : variables) {
			assignment[var] = rand() % 2;
		}
		//set the pure variables
		for (int var : positivePure) {
			assignment[var] = true;
		}
		for (int var : negativePure) {
			assignment[var] = false;
		}
		return true;
	}

	void constructVar2ClauseIndices() {
		for (size_t i = 0; i < clauses.size(); ++i) {
			vector<int> clause = clauses[i];
			for (int var : clause) {
				var2ClauseIndices[abs(var)].push_back(i);
			}
		}
	}

	void show() {
		if (!validAssignment) {
			cout << "No Satisfying Assignment Found\n";
		}
		else {
			printAssignment();
		}
	}

	void testSpeed() {
		int a = 0;
		//printClauses();
		for (int i = 0; i < 1000; i++) {
			//unsatisfiedClauses();
			/*for (vector<int>& clause : clauses) {
				for (int var : clause) {
					assignment[abs(var)] = true;
					a++;
				}
			}*/
			/*for (size_t i = 0; i < clauses.size(); ++i) {
				vector<int>& clause = clauses[i];
				for (size_t i2 = 0; i2 < clause.size(); ++i2) {
					assignment[abs(clause[i2])] = true;
					a++;
				}
			}*/
			/*for (vector<vector<int>>::iterator it = clauses.begin(); it != clauses.end(); ++it) {
				vector<int> clause = *it;
				for (vector<int>::iterator it2 = clause.begin(); it2 != clause.end(); ++it2) {
					assignment[abs(*it2)] = true;
					a++;
				}
			}*/
		}
		cout << a << "\n";
	}

};



int main(int argc, char** argv) {
	cout << "Starting Walk Sat Program\n";
	WalkSat sat;
	if (argc == 2) {
		sat.loadFile(argv[1]);
		sat.constructVar2ClauseIndices();
		sat.solve(0.5, 10000);
		sat.show();
		//sat.testSpeed();
	}
	else {
		cout << "Please provide path to file!\n";
	}
}