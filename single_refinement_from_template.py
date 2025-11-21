import os
import subprocess
import sys
import time

import collections
import itertools

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

input_path = os.path.join(script_dir, "encoding.cnf")
output_path = os.path.join(script_dir, "lines.txt")

kissat_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

if len(sys.argv) < 2:
	print("Usage: python3 generate.py <template_id>\n") 
	sys.exit(1)
	
candidate_lines_path = os.path.join(script_dir, "candidate_lines", str(sys.argv[1])+"-candidate_lines.txt")
	
start_time = time.time()
dimacs_elapsed = 0
kissat_elapsed = 0

clauses = []
variableCount = 0

candidate_lines = [[], []] # Relational, Non-relational
candidate_line_count = 0
order = 10

def addClause(variables):
	if len(variables) == 0: 
		return False
	clause = ""
	for v in variables:
		clause += str(v) + " "
	clauses.append(clause + "0")
	return True

def addImplicationClause(antecedent, consequent): # conjunction(AND) of all antecedental variables implies the disjunction(OR) of consequental variables, e.g. "x1 and .. and xn" implies "y1 or ... or yn"
	clause = "" # X implies Y is equivalent to -X OR Y
	for x in antecedent:
		clause += str(-x) + " "
	for y in consequent:
		clause += str(y) + " "
	clauses.append(clause + "0")
	return True

def addCardinalityClauses(variables, mininum, maximum): # <= maximum variables and >= minimum values are true (latin squares would use minimum = maximum = 1 for each symbol)
	global variableCount
	
	n = len(variables) # rows
	k = maximum + 1	   # columns
	l = mininum
	
	s = [] # Boolean counter variables, s[i][j] says at least j of the variables x1, ..., xi are assigned to true
	for i in range(n + 1):
		row = []
		for j in range(k + 1):
			variableCount += 1
			row.append(variableCount)
		s.append(row)
	
	for i in range(n+1):
		addClause([s[i][0]]) # 0 variables are always true of variables [x1, ..., xi]
	for j in range(1, k+1):
		addClause([-s[0][j]]) # j>=1 of nothing is always false
	for j in range(1, l+1):
		addClause([s[n][j]]) # at least minimum of [x0, ..., xi-1] are true
	for i in range(1, n+1):
		addClause([-s[i][k]]) # at most maximum of [x0, ..., xi-1] are true
		
	for i in range(1, n+1): # for each variable xi, propagate counts across the table
		for j in range(1, k+1):
			addImplicationClause([s[i-1][j]], [s[i][j]]) # If at least j of the first i-1 variables are true, then at least j of the first i variables are true
			addImplicationClause([variables[i-1], s[i-1][j-1]], [s[i][j]]) # If xi is true and at least j-1 of the first i-1 variables are true, then at least j of the first i variables are true
			if j <= l:
				addImplicationClause([s[i][j]], [s[i-1][j], variables[i-1]]) # If at least j of the first i variables are true, then either xi is true or at least j of the first i-1 variables were already true
				addImplicationClause([s[i][j]], [s[i-1][j-1]]) # If at least j of the first i variables are true, then at least j-1 of the first i-1 variables must be true

def getCombinations(totalList, array, n, currentRemovals): # n >= 0, generate all possible combinations from n choices
	if n == 0:
		totalList.append(currentRemovals)
	else: 
		for i in range(len(array)):
			tmpList = array[i + 1 : len(array)]
			removals = currentRemovals.copy()
			removals.append(array[i])
			getCombinations(totalList, tmpList, n - 1, removals)

def addXORClauses(chain): # create XOR clauses for given chain, should add 2^(len(chain) - 1) clauses for XOR
	for notCount in range(1, len(chain) + 1, 2):
		total = []
		getCombinations(total, list(range(len(chain))), notCount, [])
		for i in range(len(total)):
			tmpChain = chain.copy()
			for j in range(len(total[i])):
				tmpChain[total[i][j]] = -tmpChain[total[i][j]]
			addClause(tmpChain)
			
point_cache = collections.defaultdict(list) 
intersection_cache = {}

def load_candidate_lines_file(file_path):
	global candidate_line_count
	with open(file_path, "r") as f:
		for line in f: 
			candidate_line = line[2:].split()
			if line.startswith("R"):
				candidate_lines[0].append(candidate_line)
			elif line.startswith("N"):
				candidate_lines[1].append(candidate_line)
			else:
				continue
			for p in candidate_line:
				point_cache[p].append(candidate_line_count)
			candidate_line_count += 1
	print("Precomputing all line intersections.")
	for lines in point_cache.values():
		if len(lines) < 2: # no intersections possible
			continue
		for i, j in itertools.combinations(lines, 2):
			key = (i, j)
			intersection_cache[key] = intersection_cache.get(key, 0) + 1

def get_intersections(i, j): 
    key = (min(i,j), max(i,j))
    return intersection_cache.get(key, 0)

def get_line(id):
	if id < len(candidate_lines[0]):
		return candidate_lines[0][id]
	else:
		id -= len(candidate_lines[0])
		return candidate_lines[1][id]
	
def get_new_var():
	global variableCount
	variableCount += 1
	return variableCount

if __name__ == "__main__": 
	print("Loading candidate lines from:", candidate_lines_path)
	load_candidate_lines_file(candidate_lines_path)
	print("Assinging variables to each candidate line.")
	#	1 <= i <= candidate_line_count, needs to immutable object so it doesnt reference same value for all entries of array
	x = [None] * candidate_line_count # x[i] = true <=> candidate i selected in net
	a = [None] * candidate_line_count # a[i] = true <=> candidate i selected for A
	b = [None] * candidate_line_count # b[i] = true <=> candidate i selected for B
	for i in range(candidate_line_count):
		x[i] = get_new_var()
	for i in range(candidate_line_count):
		a[i] = get_new_var()
	for i in range(candidate_line_count):
		b[i] = get_new_var()
	# variable count is now 3 * candidate_line_count   

	print("Setting up equivalences between parallel classes and disjoint relationship.")
	for i in range(candidate_line_count): # set up equivalences
		addImplicationClause([a[i]], [x[i]]) # if ai is chosen then xi is chosen
		addImplicationClause([b[i]], [x[i]]) # if bi is chosen then xi is chosen
		addImplicationClause([x[i]], [a[i], b[i]]) # if xi is chosen then either ai is chosen or bi is chosen
		addClause([-a[i], -b[i]]) # A and B disjoint on same candidate line, e.g. not (ai and bi)

	R_indices = [i for i in range(len(candidate_lines[0]))]
	N_indices = [i for i in range(len(candidate_lines[0]), candidate_line_count)]

	print("Setting cardinality constraints, enforcing a selection of 20 lines in total, and 10 for each parallel class.")
	addCardinalityClauses([x[i] for i in range(candidate_line_count)], 20, 20)
	addCardinalityClauses([a[i] for i in range(candidate_line_count)], 10, 10)
	addCardinalityClauses([b[i] for i in range(candidate_line_count)], 10, 10)

	print("Furthering cardinality constraints, enforcing 4 relation and 6 non-relation lines for each parallel class.")
	# ensure that A selects 4 relational and 6 non relation lines
	addCardinalityClauses([a[i] for i in R_indices], 4, 4)
	addCardinalityClauses([a[i] for i in N_indices], 6, 6)
	# ensure that B selects 4 relational and 6 non relation lines
	addCardinalityClauses([b[i] for i in R_indices], 4, 4)
	addCardinalityClauses([b[i] for i in N_indices], 6, 6)

	print("Forbidding parallel classes from intersecting within each other.")
	for i in range(candidate_line_count): # forbid parallel classes from having lines that intersection each other
		for j in range(i+1, candidate_line_count):
			if get_intersections(i, j) > 0:
				addClause([-a[i], -a[j]])
				addClause([-b[i], -b[j]])

	print("Enforcing exactly one intersection for each line in one parallel class to the other.")
	for i in range(candidate_line_count): # A's candidate lines each intersect a line in B once
		InterB = [j for j in range(candidate_line_count) if get_intersections(i, j) == 1]
		if not len(InterB): # no compatible B to intersect exactly once -> cannot choose a_i
			addClause([-a[i]])
		else: # at least one: (-a_i OR b_j1 OR b_j2 OR ...)
			addImplicationClause([a[i]], [b[j] for j in InterB])
			for p, q in itertools.combinations(InterB, 2):
				addClause([-a[i], -b[p], -b[q]])
	for j in range(candidate_line_count): # B's candidate lines each intersect a line in A once
		InterA = [i for i in range(candidate_line_count) if get_intersections(i, j) == 1]
		if not len(InterA):
			addClause([-b[j]])
		else:
			addImplicationClause([b[j]], [a[i] for i in InterA])
			for p, q in itertools.combinations(InterA, 2):
				addClause([-b[j], -a[p], -a[q]])

	clauseCount = len(clauses)
	with open(input_path, "w") as f:
		f.write(f"p cnf {variableCount} {len(clauses)}\n")
		f.write("\n".join(clauses))
			
	dimacs_elapsed = round((time.time() - start_time) * 100)/100
	print("Wrote DIMACS CNF file to:", input_path)  

	kissat_time = time.time() # wall time
	with open(output_path, "w") as out_file:
		commands = [kissat_path, input_path]
		subprocess.run(commands, stdout=out_file, stderr=subprocess.STDOUT)
	kissat_elapsed = round((time.time() - kissat_time) * 100)/100
	print("Wrote output to:", output_path)

	print("\nTotal elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
	print("     Dimacs elapsed time:", dimacs_elapsed, "seconds")
	print("     SAT Solver elapsed time:", kissat_elapsed, "seconds")

# x_i = true implies candidate line i is in the net for all 1 <= i <= candidate_line_count
# A implies 10 candidate lines, 4 relation and 6 non relation
# B implies 10 candidate lines, 4 relation and 6 non relation
# A's candidate lines do not intersect each other
# B's candidate lines do not intersect each other
# A's candidate lines each intersect a line in B once
# B's candidate lines each intersect a line in A once
# A and B do not share the same candidate lines

# I might need to add in the lines from parallel class 0 and 1 to add orthogonality property between lines from these parllel classes and the 2 new ones we are making
#   Similarly, two lines ℓ1 and ℓ2 are orthogonal if |ℓ1 ∩ ℓ2| = 1. A k-net(n) is a partial linear space N = (P, L) consisting of a set P of n 2 points and a set L of kn lines, 
#   such that each line is incident with n points and each point is incident with k lines.