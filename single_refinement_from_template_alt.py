import os
import subprocess
import sys
import time

import shutil

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

input_path = os.path.join(script_dir, "encoding.cnf")
output_path = os.path.join(script_dir, "lines.txt")

satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")
#satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")

if len(sys.argv) < 2:
	print("Usage: python3 generate.py <template_id>\n") 
	sys.exit(1)
	
template_path = os.path.join(script_dir, "templates", str(int(sys.argv[1])+1)+"-template.txt")
	
start_time = time.time()
dimacs_elapsed = 0
prepend_elapsed = 0
kissat_elapsed = 0
verify_time = 0

addTemplateClauses = True # Creates clauses to enforce template's relations

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

def getNewVariable():
	global variableCount
	variableCount += 1
	return variableCount

def unloadTemplate(path):
	template = [[], []]
	with open(path, "r") as f:
		for i, line in enumerate(f):
			line = line.strip()
			if len(line) > 0:
				if i <= 9:
					template[0].append([])
					for s in list(line):
						template[0][-1].append(int(s))
				if i > 10 and i <= 20:
					template[1].append([])
					for s in list(line):
						template[1][-1].append(int(s))
	return template

if __name__ == "__main__": 
	def checkValid(square):
		n = len(square)
		if any(len(row) != n for row in square): # All rows are length n
			return False
		for row in square: # Each row contains all symbols 0 to n-1 exactly once
			if sorted(row) != list(range(n)):
				return False
		for col_idx in range(n): # Each column contains all symbols 0 to n-1 exactly once
			col = [square[row_idx][col_idx] for row_idx in range(n)]
			if sorted(col) != list(range(n)):
				return False
		return True
	def checkOrthogonal(squares):
		square1 = squares[order:order*2] # Q
		square2 = squares[order*2:order*3] # Z
		exists = []
		for i in range(order):
			for j in range(order):
				pair = (square1[i][j], square2[i][j])
				if pair in exists:
					return False
				exists.append(pair)
		return True
	
	def get1DIndex(l, r, c, s): # 4n by n^2 matrix
		index = latin_squares * order * order * r # Split net encoding into n blocks, go the the rth block
		index += latin_squares * order * c # Split each block into n subblocks, go the cth subblock
		index += order * l # Skip position data and redundant latin square (e.g. row and column squares)
		index += s # Pick symbol we're at
		return index + 1
	
	def get4DIndex(index): 
		index = index - 1
		r = index // (latin_squares * order * order)
		index -= r * (latin_squares * order * order)
		c = index // (latin_squares * order)
		index -= c * (latin_squares * order)
		l = index // order
		index -= l * order
		return l, r, c, index

	open(input_path, 'w').close()

	template = unloadTemplate(template_path)
	latin_squares = 3
	variableCount = get1DIndex(latin_squares - 1, order - 1, order - 1, order - 1) 
	
	if addTemplateClauses: # doesnt immedately return UNSAT for templates with 0 refinements
		for par_class, lines in enumerate(template):
			for row, line in enumerate(lines):
				print(f"P_{par_class}, Row {row}: {line}")
				for col, relational in enumerate(line):
					if relational == 1:
						print(f"({row}, {col}) Relational ({relational})")
						for s in range(4,order):
							addClause([-get1DIndex(par_class, row, col, s)])
						allow = []
						for s in range(4):
							allow.append(get1DIndex(par_class, row, col, s))
							for t in range(s+1, 4): # at most one
								addClause([-get1DIndex(par_class, row, col, s), -get1DIndex(par_class, row, col, t)])
						addClause(allow) # at least one
					else:
						print(f"({row}, {col}) Non-Relational ({relational})")
						for s in range(4):
							addClause([-get1DIndex(par_class, row, col, s)])
						allow = []
						for s in range(4,order):
							allow.append(get1DIndex(par_class, row, col, s))
							for t in range(s+1, order): # at most one
								addClause([-get1DIndex(par_class, row, col, s), -get1DIndex(par_class, row, col, t)])
						addClause(allow) # at least one 
				print()

	for l in range(latin_squares): # Maintain latin square clauses
		for x in range(order):
			for y in range(order): # Create at least one value clause for row, col and symbol
				clause1 = [] # row
				clause2 = [] # col
				clause3 = [] # sym
				for z in range(order):
					clause1.append(get1DIndex(l, x,y,z))
					clause2.append(get1DIndex(l, x,z,y))
					clause3.append(get1DIndex(l, z,x,y))
					for w in range(z + 1, order): # At most one symbol (binary exclusions)
						addClause([-get1DIndex(l, x,y,z), -get1DIndex(l, x,y,w)])
						addClause([-get1DIndex(l, x,z,y), -get1DIndex(l, x,w,y)])
						addClause([-get1DIndex(l, z,x,y), -get1DIndex(l, w,x,y)])
				addClause(clause1)
				addClause(clause2)
				addClause(clause3)
	
	for i in range(order): # orthogonality using auxiliary
		for i_prime in range(order):
			for j in range(order):
				for k in range(order):
					P, Q, Z = get1DIndex(0, i_prime,j,k), get1DIndex(1, i,j,k), get1DIndex(2, i,j,i_prime)
					addImplicationClause([Z, P], [Q])
					addImplicationClause([Z, Q], [P])
					addImplicationClause([P, Q], [Z])

	'''
	Maybe we could encode the the symmetry breaking propositions presented in the Myrvolds Paper? Need to prove we can
	'''

	dumpClauses()
	print(f"Total of {variableCount} variables and {clauseCount} clauses.")
	
	dimacs_elapsed = round((time.time() - start_time) * 100)/100

	prepend_to_file_with_temp(input_path, f"p cnf {variableCount} {clauseCount}\n") # worse case for clause count is between 9 and 12 billion clauses
			
	prepend_elapsed = round((time.time() - start_time) * 100)/100 - dimacs_elapsed

	print("Wrote DIMACS CNF file to:", input_path)  

	with open(output_path, "w") as out_file:
		commands = [satsolver_path, input_path]
		subprocess.run(commands, stdout=out_file, stderr=subprocess.STDOUT)
	verify_time = time.time()
	print("Wrote output to:", output_path)

	with open(output_path, "r") as f:
		combinedLatinSquares = [] 
		for square in range(latin_squares * order):
			combinedLatinSquares.append([])
			for row in range(order):
				combinedLatinSquares[square].append(-1) # easily tells us if logic error occured by the existance of -1 symbol

		satisfiable = None
		for line in f:
			if line.startswith("c process-time:"):
				kissat_elapsed = line.split()[-2]
			elif line.startswith("s "):
				if "UNSATISFIABLE" in line:
					satisfiable = "UNSAT"
				elif "SATISFIABLE" in line:
					satisfiable = "SAT"
			elif line.startswith("v "):
				values = line[2:].strip().split()
				for val in values:
					if val == '0': # End of variables
						break
					val = int(val)
					if val > 0:
						l, r, c, s = get4DIndex(val)
						combinedLatinSquares[r + l * order][c] = s

		print("Result:", satisfiable)
		colours = []
		def getRowColour(row):
			colour = 40 + row
			if colour >= 47:
				colour += 53
			return colour
		if satisfiable == "SAT":
			print(f"\n(P, Q) is a transversal representation pair of Latin squares of order {order}.")
			print("Each transversal of Q is highlighted in its own unique colour, the transversals' row representations are given by P.")

			for row in range(order*3):
				if row % order == 0:
					print("\n\033[39m" + (["P", "Q", "Z"][row//order]) + ":")
				if row < order: # print row representation of the transversal in the TRP
					print(f"\033[{getRowColour(row)}m\033[97m{combinedLatinSquares[row]}\033[39m\033[49m")
				elif row < 2*order: # print latin square Q with colouring each symbol in the TRP
					for col in range(order):
						symbol = combinedLatinSquares[row][col]
						nrow = 0
						for i in range(order):
							if combinedLatinSquares[i][col] == symbol:
								nrow = i
								break
						if col == 0:
							print("[", end="")
						print(f"\033[{getRowColour(nrow)}m\033[97m{symbol}", end="")
						if col == order - 1:
							print("\033[39m\033[49m]")
						else:
							print(", ", end="")
				else:
					print(combinedLatinSquares[row])
			if not (checkValid(combinedLatinSquares[0 : order]) and checkValid(combinedLatinSquares[order : order*2]) and checkValid(combinedLatinSquares[order*2 : order*3])):
				print("\nInvalid latin squares produced by SAT Solver for latin squares of order", str(order) + ".")
			elif checkOrthogonal(combinedLatinSquares):
				print("\nValid orthogonal solution produced by SAT Solver for latin squares of order", str(order) + ".")
			else:
				print("\nInvalid orthogonal solution produced by SAT Solver")
	verify_elapsed = round((time.time() - verify_time) * 100)/100

	print("\nTotal elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
	print("     Dimacs elapsed time:", dimacs_elapsed, "seconds")
	print("     Prepend elapsed time:", prepend_elapsed, "seconds")
	print("     SAT Solver elapsed time:", kissat_elapsed, "seconds")
	print("     Verification elapsed time:", verify_elapsed, "seconds")

# cd /mnt/g/Code/sat\ solver\ stuff/refinements\ and\ candidate\ lines