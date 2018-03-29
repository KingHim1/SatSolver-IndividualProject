# parsing in python
# 
# format: (c = comment, p CNF = conjunctive normal form)
# c
# c start with comments
# c
# c 
# p cnf 5 3
# 1 -5 4 0
# -1 5 3 4 0
# -3 -4 0

def parseDataFile(filePath):
    dataFile = open(filePath, "r")
    data = dataFile.read()
    data = data.rstrip()
    data = data.split("\n")
    nbvar = 0
    nbclause = 0
    clauses = []
    for line in data:
        #       this line is a comment in the file - can ignore!
        if line[0] == "c":
            print(line[0])
        #       p cnf nbvar nbclauses
        #       cnf = the data type; nbvar = upper bound on the largest index of a variable, and nbclause = number of clauses in the file
        elif line[0] == "p":
            values = line.split()
            nbvar = int(values[2])
            nbclause = int(values[3])
        elif line[0] == "-" or (line[0].isdigit() and int(line[0]) != 0):
        #       2D array of clauses, inside array is the disjunction of variables
            clause = line.split()
            for x in range(0, len(clause)):
                clause[x] = int(clause[x])
            clauses.append(clause)
    return [nbvar, nbclause, clauses]

# parseDataFile("test.txt")
