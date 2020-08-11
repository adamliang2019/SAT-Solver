import sys
import random
"""
      k: # of literals per clause
      m: # of clauses to generate
      n: # of symbols
"""
def rand_cnf_generator(k, m, n):
    #can't have clause length longer than # symbols and can't have more symbols than variables used
    assert(int(k)<=int(n))
    assert(int(n)<=int(m)*int(k))

    symbols = list(range(1, int(n)+1))
    #writing header
    text_file = open("generated_cnf.txt", "w")
    text_file.write("c this is a generated file\np cnf " + n + " " + m +"\n")
    clauses = []
    # make sure that all the symbols are used in the clauses (repeat until true)
    used = set()
    while(not all(var in used for var in symbols)):
        used.clear()
        for c in range(0, int(m)):
            #makes sure no duplicate symbols in clause
            available_symbols = symbols[:]
            clause = ""
            for v in range(0, int(k)):
                variable = random.choice(available_symbols)
                available_symbols.remove(variable)
                used.add(variable)
                sign = random.choice([-1,1])
                variable *= sign;
                clause += str(variable) + " "
            clauses.append(clause)
    text_file.write("0\n".join(clauses))
    text_file.write("0\n")
    text_file.close();

if __name__ == '__main__':
    k = sys.argv[1]
    m = sys.argv[2]
    n = sys.argv[3]
    rand_cnf_generator(k, m, n)
