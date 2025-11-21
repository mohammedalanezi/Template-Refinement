import os
import subprocess
import sys
import time

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

input_path = os.path.join(script_dir, "encoding.cnf")
output_path = os.path.join(script_dir, "lines.txt")

kissat_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust") # Before testing: Update this to your sat solver's location 

if len(sys.argv) < 3:
	print("Usage: python3 generate.py <template_file> <frequency_square> [in_relation]\n") 
	sys.exit(1)
	
template_path = os.path.join(script_dir, "source", sys.argv[1])
trivial_template_path = os.path.join(script_dir, "source", "trivial_template.txt")
	
start_time = time.time()
dimacs_elapsed = 0
kissat_elapsed = 0

clauses = []
variableCount = 0

template = []
order = 10
frequency_square = int(sys.argv[2]) + 2 # 0 - 1
relational_lines = True # only produce relational lines
if len(sys.argv) >= 4:
	relational_lines = str.lower(sys.argv[3]) == "true"

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

def load_template_file(file_path):
	with open(file_path, "r") as f:
		current_square = len(template)
		current_line = 0
		template.append([])
		for line in f: 
			if current_line == 10:
				current_line = 0
				current_square += 1 
				template.append([])
			line = line.strip()
			line = [int(x) for x in line] # Converts line into list of variables
			if len(line) > 0:
				template[current_square].append(line)
				current_line += 1

if __name__ == "__main__": 
	def get1DIndex(r, c):
		return r * order + c + 1
	
	load_template_file(trivial_template_path)
	load_template_file(template_path)

	def getTemplateBit(r, c, bit):
		if (r < 0 or r >= order) or (c < 0 or c >= order) or (bit < 0 or bit >= order):
			raise TypeError(f"Attempted to get bit at ({r},{c},{bit}), which is out of bounds, must be witin {0} and {order} for each position.")
		return template[bit][r][c]
	variableCount = get1DIndex(order-1, order-1) 
	exhaustive_variables = variableCount
	for x in range(order): # Make sure variables form a row and column monomial matrix (Permutation matrix)
		row_vars = [get1DIndex(x, c) for c in range(order)]
		addCardinalityClauses(row_vars, 1, 1)
		col_vars = [get1DIndex(r, x) for r in range(order)]
		addCardinalityClauses(col_vars, 1, 1)
	
	num_bits = len(template)
	weight_buckets = {} # enforce weight 22 for relational and weight 12 for non-relational (with our desired weights for each point in the line)
	for weight in range(num_bits + 1):
		weight_buckets[weight] = []
	
	for r in range(order): # only include relational or non-relation points
		for c in range(order):
			weight = sum(getTemplateBit(r, c, b) for b in range(num_bits))
			if relational_lines == True:
				if getTemplateBit(r, c, frequency_square) == 0:
					addClause([-get1DIndex(r,c)])
				else:
					weight_buckets[weight].append(get1DIndex(r, c))
			elif relational_lines == False:
				if getTemplateBit(r, c, frequency_square) == 1:
					addClause([-get1DIndex(r,c)])
				else:
					weight_buckets[weight].append(get1DIndex(r, c))
					
	if relational_lines == True:
		addCardinalityClauses(weight_buckets.get(4, []), 1, 1)  # exactly one weight-4
		addCardinalityClauses(weight_buckets.get(2, []), 9, 9)  # exactly nine weight-2
	elif relational_lines == False:
		addCardinalityClauses(weight_buckets.get(2, []), 6, 6)  # exactly six weight-2
		addCardinalityClauses(weight_buckets.get(0, []), 4, 4)  # exactly four weight-0

	clauseCount = len(clauses)
	with open(input_path, "w") as f:
		f.write(f"p cnf {variableCount} {clauseCount}\n")
		f.write("\n".join(clauses))
			
	dimacs_elapsed = round((time.time() - start_time) * 100)/100
	print("Wrote DIMACS CNF file to:", input_path)  

	kissat_time = time.time()
	with open(output_path, "w") as out_file:
		commands = [kissat_path, input_path, "--order", str(exhaustive_variables)]
		subprocess.run(commands, stdout=out_file, stderr=subprocess.STDOUT)
	kissat_elapsed = round((time.time() - kissat_time) * 100)/100
	print("Wrote output to:", output_path)

	with open(output_path, 'r') as f:
		for line in f:
			if line.startswith("c Number of solutions:"):
				solutions = line[23:-1]

	print(f"Found {solutions} {"" if relational_lines==True else "non-"}relational candidate lines.")

	print("\nTotal elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
	print("     Dimacs elapsed time:", dimacs_elapsed, "seconds")
	print("     SAT Solver elapsed time:", kissat_elapsed, "seconds")

# cd /mnt/g/Code/sat\ solver\ stuff/search\ templates