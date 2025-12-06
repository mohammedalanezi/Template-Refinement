import os
import subprocess
import sys
import time

import collections
import itertools
import shutil
from collections import defaultdict

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

input_path = os.path.join(script_dir, "encoding.cnf")
output_path = os.path.join(script_dir, "lines.txt")

satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

if len(sys.argv) < 2:
	print("Usage: python3 generate.py <template_id>\n") 
	sys.exit(1)
	
candidate_lines_2_path = os.path.join(script_dir, "2-candidate_lines", str(sys.argv[1])+"-candidate_lines.txt")
candidate_lines_3_path = os.path.join(script_dir, "3-candidate_lines", str(sys.argv[1])+"-candidate_lines.txt")
	
start_time = time.time()
dimacs_elapsed = 0
prepend_elapsed = 0
kissat_elapsed = 0

clauses = []
variableCount = 0
clauseCount = 0

points = [set(), set()]
candidate_lines = [[[], []], [[], []]] # Relational, Non-relational
candidate_line_count = [0, 0]
order = 10

def prepend_to_file_with_temp(filepath, content_to_prepend):
	temp_filepath = filepath + ".tmp"
	with open(temp_filepath, 'w') as temp:
		temp.write(content_to_prepend)
		with open(filepath, 'r') as f:
			shutil.copyfileobj(f, temp, length=1024*1024)  # 1MB buffer
	os.replace(temp_filepath, filepath) # replaces original file with temporary one

def dumpClauses():
	global clauses
	with open(input_path, "a") as f:
		for line in clauses:
			f.write(line + "0\n")
	clauses.clear()

def writeClause(clause):
	global clauseCount
	global clauses
	clauseCount += 1
	clauses.append(clause)
	if len(clauses) > 100000:
		with open(input_path, "a") as f:
			for line in clauses:
				f.write(line + "0\n")
		clauses.clear()

def addClause(variables):
	if len(variables) == 0: 
		return False
	clause = ""
	for v in variables:
		clause += str(v) + " "
	writeClause(clause)
	return True

def addImplicationClause(antecedent, consequent): # conjunction(AND) of all antecedental variables implies the disjunction(OR) of consequental variables, e.g. "x1 and .. and xn" implies "y1 or ... or yn"
	clause = "" # X implies Y is equivalent to -X OR Y
	for x in antecedent:
		clause += str(-x) + " "
	for y in consequent:
		clause += str(y) + " "
	writeClause(clause)
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

def load_candidate_lines_file(file_path, p):
	global candidate_line_count
	with open(file_path, "r") as f:
		for line in f: 
			candidate_line = line[2:].split()
			if line.startswith("R"):
				candidate_lines[p][0].append(candidate_line)
			elif line.startswith("N"):
				candidate_lines[p][1].append(candidate_line)
			else:
				continue
			candidate_line_count[p] += 1
			for point in candidate_line:
				points[p].add(point)

def getLine(id, p):
	if id < len(candidate_lines[p][0]):
		return candidate_lines[p][0][id]
	else:
		id -= len(candidate_lines[p][0])
		return candidate_lines[p][1][id]
	
def getNewVariable():
	global variableCount
	variableCount += 1
	return variableCount

if __name__ == "__main__": 
	open(input_path, 'w').close()
	print("Loading candidate lines from:", candidate_lines_2_path)
	load_candidate_lines_file(candidate_lines_2_path, 0)
	print("Loading candidate lines from:", candidate_lines_3_path)
	load_candidate_lines_file(candidate_lines_3_path, 1)

	A_sets = [set(getLine(i,0)) for i in range(candidate_line_count[0])]
	B_sets = [set(getLine(j,1)) for j in range(candidate_line_count[1])]
	
	def getIntersections(i, j, p1, p2): 
		line_i = None
		line_j = None
		if p1 == 0:
			line_i = A_sets[i]
		else:
			line_i = B_sets[i]
		if p2 == 0:
			line_j = A_sets[j]
		else:
			line_j = B_sets[j]
		return len(line_i & line_j)

	print("Assinging variables to each candidate line.")
	#	1 <= i <= candidate_line_count, needs to immutable object so it doesnt reference same value for all entries of array
	a = [None] * candidate_line_count[0] # a[i] = true <=> candidate i selected for A
	b = [None] * candidate_line_count[1] # b[i] = true <=> candidate i selected for B
	for i in range(candidate_line_count[0]):
		a[i] = getNewVariable()
	for i in range(candidate_line_count[1]):
		b[i] = getNewVariable()
	exhaustive_variables = variableCount
	total_points = points[0] | points[1] # points in A or B
	# variable count is now 2 * candidate_line_count

	point_to_A = defaultdict(list)
	point_to_B = defaultdict(list)
	for i in range(candidate_line_count[0]):
		line = getLine(i, 0)
		for p in line:
			point_to_A[p].append(i)
	for j in range(candidate_line_count[1]):
		line = getLine(j, 1)
		for p in line:
			point_to_B[p].append(j)

	print("Enforcing coverage of each point by exactly one line.")
	for p in total_points: # at least 1 line for each point must be selected, ~2,315,680 clauses
		a_indices = point_to_A.get(p, [])
		b_indices = point_to_B.get(p, [])
		if a_indices:
			addCardinalityClauses([a[i] for i in a_indices], 1, 1)
		if b_indices: 
			addCardinalityClauses([b[j] for j in b_indices], 1, 1)
	
	print("Enforcing exactly one intersection for each line in one parallel class to the other.")
	for i in range(candidate_line_count[0]): # worst case ~9604 to ~12544 million clauses twice
		for j in range(candidate_line_count[1]): 
			intersections_01 = getIntersections(i, j, 0, 1)
			if intersections_01 != 1: # ensure each line selected is incident once to another in the other parallel class
				addImplicationClause([a[i]], [-b[j]])
		if i % 1000 == 0:
			print(f"{i}/{candidate_line_count[0]}")

	dumpClauses()
	print(f"Total of {variableCount} variables and {clauseCount} clauses.")
	
	dimacs_elapsed = round((time.time() - start_time) * 100)/100

	prepend_to_file_with_temp(input_path, f"p cnf {variableCount} {clauseCount}\n") # worse case for clause count is between 9 and 12 billion clauses
			
	prepend_elapsed = round((time.time() - start_time) * 100)/100 - dimacs_elapsed

	print("Wrote DIMACS CNF file to:", input_path)  

	kissat_time = time.time() # wall time
	with open(output_path, "w") as out_file:
		#commands = [satsolver_path, input_path]
		commands = [satsolver_path, input_path, "--only-neg", "--order", str(exhaustive_variables)]
		subprocess.run(commands, stdout=out_file, stderr=subprocess.STDOUT)
	kissat_elapsed = round((time.time() - kissat_time) * 100)/100
	print("Wrote output to:", output_path)

	with open(output_path, "r") as f:
		for line in f:
			if line.startswith("s UNSATISFIABLE"):
				print("\nUNSATISFIABLE")
				break
			if line.startswith("s SATISFIABLE"):
				print("\nSATISFIABLE")
				break

	print("\nTotal elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
	print("     Dimacs elapsed time:", dimacs_elapsed, "seconds")
	print("     Prepend elapsed time:", prepend_elapsed, "seconds")
	print("     SAT Solver elapsed time:", kissat_elapsed, "seconds")

# cd /mnt/g/Code/sat\ solver\ stuff/refinements\ and\ candidate\ lines
