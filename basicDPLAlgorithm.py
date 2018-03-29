import parseDataFile
import sys
from random import randint
import copy
#
# General Sections of the DPL Algorithm
#

#Decide
#Decide the variable to assign

#Deduce
#Deduce any unit clauses formed from the decide stage

#Diagnose
#Add any new clauses deduced to the clause database

#Erase
#Backtracking when a conflict occurs

# ------------------------------------------------------------------------
# ------------------------------------------------------------------------

#
# Basic Depth First Search DPL Algorithm
#

#Parse data file
file = str(sys.argv[1])
print(file)
data = parseDataFile.parseDataFile(file)
nbvar = data[0]
nbclause = data[1]
clauses = copy.deepcopy(data[2])
print(clauses)
#TODO -- Need to find out how to EFFICIENTLY check all clauses for unit clause and remove variables due to unit clause being found...

def getNewLiteral(untestedLiterals, literals, nbvar):
    if len(untestedLiterals) > 1:
        x = randint(0, len(untestedLiterals)-1)
        literal = untestedLiterals[x]
#        untestedLiterals.remove(untestedLiterals[x])
        return literal
    elif len(untestedLiterals) == 1:
        literal = untestedLiterals[0]
#        untestedLiterals.remove(literal)
        return literal
    else:
        return False


def unitPropagation(nbvar, untestedLiterals, literals, clauses):
    # print(clauses)
    clauseCopy = copy.deepcopy(clauses)
    numOfUnitClauses = 1
    while numOfUnitClauses > 0:
        numOfUnitClauses = 0
        for clause in clauseCopy:
            if len(clause) == 1:
                return False
            elif len(clause) == 2:
                if abs(clause[0]) in untestedLiterals:
                    literals.append(clause[0])
                    untestedLiterals.remove(abs(clause[0]))
                    numOfUnitClauses += 1
                    clauseCopy = [c for c in clauseCopy if clause[0] not in c]
                    for cl in clauseCopy:
                        if -clause[0] in cl:
                            cl.remove(-clause[0])
    return ([clauseCopy, literals, untestedLiterals])


def DPLAlgorithm(nbvar, untestedLiterals, literals, clauses):
    #Initial Unit propagation - Deduce
    clauseAndLiteralsAndUntestedLiterals = unitPropagation(nbvar, untestedLiterals, literals, clauses)
    if isinstance(clauseAndLiteralsAndUntestedLiterals, bool):
        return False
    cls = clauseAndLiteralsAndUntestedLiterals[0]
    literals = clauseAndLiteralsAndUntestedLiterals[1]
    untestedLiterals = clauseAndLiteralsAndUntestedLiterals[2]
    if len(cls) == 0:
        return literals
    #Decide literals
    literal = getNewLiteral(untestedLiterals, literals, nbvar)
    if not isinstance(literal, (bool)):
        cls.append([literal,0])
    else:
        return False
    #Recursive call of algorithm for literal and the negation of the literal
#    print("split1")
    untestedLiteralsCopy1 = copy.deepcopy(untestedLiterals)
    untestedLiteralsCopy2 = copy.deepcopy(untestedLiterals)
    literalsCopy1 = copy.deepcopy(literals)
    literalsCopy2 = copy.deepcopy(literals)
    literalsOrFalse = (DPLAlgorithm(nbvar, untestedLiteralsCopy1, literalsCopy1, cls))
    if not isinstance(literalsOrFalse, (bool)):
        return literalsOrFalse
    else:
        cls.remove([literal,0])
        cls.append([-literal,0])
#        print("split2")
        literalsOrFalse = (DPLAlgorithm(nbvar, untestedLiteralsCopy2, literalsCopy2, cls))
        if not isinstance(literalsOrFalse, (bool)):
            return literalsOrFalse
        else:
            return False

#Running the basic DPLL algorithm
#nbvar = 8
literals = []
untestedLiterals = [x for x in range(1, nbvar+1)]
#print(clauses)
#z = (DPLAlgorithm(nbvar, untestedLiterals, literals, clauses))
#print(z)
#
#def absoluteVal(elem):
#    return abs(elem)
#
#z.sort(key = absoluteVal)
#print(z)
#print(len(z))



# ------------------------------------------------------------------------
# ------------------------------------------------------------------------

def testSatisfiableWithLiterals(nbvar, literals, clause):
    untestedLiterals = [x for x in range(1, nbvar+1)]
    lit = []
    for l in range(0, len(literals)):
        if literals[l] == 1:
            clause.append([l+1,0])
        else:
            clause.append([-(l+1),0])
    clauseAndLiteralsAndUntestedLiterals = unitPropagation(nbvar, untestedLiterals, lit, clause)
    return (clauseAndLiteralsAndUntestedLiterals)

"""
    CDCL(φ, ν)
    if (UnitPropagation(φ, ν ) == CONFLICT)
        then return UNSAT
    dl ← 0                                                      Decision level
    while (not AllVariablesAssigned(φ, ν ))
        do (x, v) = PickBranchingVariable(φ, ν)
        dl ← dl + 1                                             Increment decision level due to new decision
        ν ← ν ∪ {(x, v)}
            if (UnitPropagation(φ, ν) == CONFLICT)
                then β = ConflictAnalysis(φ, ν)
                if (β < 0)                                      Diagnose stage
                    then return UNSAT
                    else Backtrack(φ, ν, β)
                        dl ← β                                  Decrement decision level due to backtracking
    return SAT
"""
#untestedLiterals = listOfVariables
#clauses = list of clauses
#nbvar = 8
listOfVariables = untestedLiterals
variableVals = ["u" for x in range(nbvar)]
variableAntecedents = [None for x in range(nbvar+1)]
variableDecisionLevels = [-1 for x in range(nbvar)]
watchedLiterals =[[[],[]] for x in range(nbvar)]
unassignedVariables = untestedLiterals
#print(variableVals)
#print(variableAntecedents)
#print(variableDecisionLevels)
#print(watchedLiterals)

def createWatchedLits(clauses, nbvar):
    # print("CREATE WATCHED LITERALS")
    watchedLiterals =[[[],[]] for x in range(nbvar)]
    for x in range(0, len(clauses)):
        firstLit = copy.deepcopy(clauses[x][0])
        secondLit = copy.deepcopy(clauses[x][1])
        if firstLit<0:
            watchedLiterals[abs(firstLit)-1][0].append(x)
        elif firstLit > 0:
            watchedLiterals[abs(firstLit)-1][1].append(x)
        if secondLit < 0:
            watchedLiterals[abs(secondLit)-1][0].append(x)
        elif secondLit > 0:
            watchedLiterals[abs(secondLit)-1][1].append(x)
    return(watchedLiterals)

def updateWatchedLits(watchedLiterals, variableValue, literal):
    # print("UPDATING WATCHED LITERALS")
    # print("Variable = " + str(abs(literal)) + "; Value = " + str(variableValue))
    if variableValue ==1:
        # print("CLAUSE NUMBERS FOR LITERAL -" + str(literal))
        # print(watchedLiterals[abs(literal)-1][0])
        clauseNumber = copy.deepcopy(watchedLiterals[abs(literal)-1][0])
        for x in clauseNumber:
            clause = clauses[x]
            # print(x)
#            previousIndex = clause.index(-abs(literal))
            if clause[0] == -abs(literal):
                previousIndex = 0
                # print("GOT 0")
            elif clause[1] == -abs(literal):
                previousIndex = 1
                # print("GOT 1")
            else:
                previousIndex = 2;
            swapped = False
            if previousIndex <= 1:
                for y in range(2, len(clause)):
                    if not swapped:
                        if (variableVals[abs(clause[y])-1] == "u" or litValue(clause[y], variableVals[abs(clause[y])-1]) == 1) and clause[y]!=0:
                            # print("ORIGINAL CLAUSE")
                            # print(clause)
                            swapped = True
#                            print(watchedLiterals[abs(literal)-1][0])
#                            print(y)
                            watchedLiterals[abs(literal)-1][0].remove(x)
                            if clause[y] < 0:
                                watchedLiterals[abs(clause[y])-1][0].append(x)
                            else:
                                watchedLiterals[abs(clause[y])-1][1].append(x)
                            temp1 = copy.deepcopy(clause[y])
                            temp2 = copy.deepcopy(clause[previousIndex])
                            clause[y] = temp2
                            clause[previousIndex]= temp1
                            # print("NEW CLAUSE")
                            # print(clauses)
                            # print(clause)
                            # print("UPDATED WATCHED LITERALS OF: " + str(literal))
                            # print(watchedLiterals[abs(clause[y])-1])
                            # print("----------")
    else:
        # print("CLAUSE NUMBERS FOR LITERAL " + str(literal))
        # print(watchedLiterals[abs(literal)-1][1])
        watchedLitsCopy = copy.deepcopy(watchedLiterals[abs(literal)-1][1])
        for clauseNum in watchedLitsCopy:
            clause = clauses[clauseNum]
            # print(clauseNum)
            swapped = False
            previousIndex = clause.index(abs(literal))
            # print("PREVIOUS INDEX:" + str(previousIndex))
            if previousIndex <= 1:
                for x in range(2, len(clause)):
                    if not swapped:
                        if (variableVals[abs(clause[x])-1] == "u" or litValue(clause[x], variableVals[abs(clause[x])-1]) == 1) and clause[x]!=0:
                            swapped = True
                            # print("ORIGINAL CLAUSE")
                            # print(clause)
                            # print("WATCHED LITERALS FOR ORIGINAL CLAUSE")
                            # print(watchedLiterals[abs(literal)-1][1])
                            watchedLiterals[abs(literal)-1][1].remove(clauseNum)
                            # print("WATCHED LITERALS AFTER CHANGING CLAUSE")
                            # print(watchedLiterals[abs(literal)-1][1])
                            if clause[x] < 0:
                                watchedLiterals[abs(clause[x])-1][0].append(clauseNum)
                                temp1 = copy.deepcopy(clause[x])
                                temp2 = copy.deepcopy(clause[previousIndex])
                                clause[x] = temp2
                                clause[previousIndex] = temp1
#                                clause[x], clause[previousIndex] = clause[previousIndex], clause[x]
                            else:
                                watchedLiterals[abs(clause[x])-1][1].append(clauseNum)
                                temp1 = copy.deepcopy(clause[x])
                                temp2 = copy.deepcopy(clause[previousIndex])
                                clause[x] = temp2
                                clause[previousIndex] = temp1
#                                clause[x], clause[previousIndex] = clause[previousIndex], clause[x]
#                             print("NEW CLAUSE")
#                             print(clause)
#                             print("UPDATED WATCHED LITERALS OF: " + str(literal))
#                             print(watchedLiterals[abs(clause[x])-1])
#                             print("CLAUSES")
#                             print(clauses)
#                             print("----------")

def watchedLitsAdd(watchedLiterals, clause, numOfClause):
    # print("ADD TO WATCHED LITERALS")
#    print(clause)
#    print(numOfClause)
#     print(clauses)
    clause.remove(0)
    clause.append(0)
    if clause[0] < 0:
        watchedLiterals[abs(clause[0])-1][0].append(numOfClause -1)
    else:
        watchedLiterals[abs(clause[0])-1][1].append(numOfClause -1)
    if clause[1] < 0:
        watchedLiterals[abs(clause[1])-1][0].append(numOfClause -1)
    else:
        watchedLiterals[abs(clause[1])-1][1].append(numOfClause -1)
    # print(watchedLiterals[abs(clause[0])-1])
    # print(watchedLiterals[abs(clause[1])-1])
    # print("START ADD")
    # for x in watchedLiterals[abs(clause[0])-1][0]:
    #     print(clauses[abs(x)])
    # for x in watchedLiterals[abs(clause[0])-1][1]:
    #     print(clauses[abs(x)])
    # for x in watchedLiterals[abs(clause[1])-1][0]:
    #     print(clauses[abs(x)])
    # for x in watchedLiterals[abs(clause[1])-1][1]:
    #     print(clauses[abs(x)])
    # print("STOP ADD")

def litValue(clauseLiteral, variableValue):
    if clauseLiteral < 0:
        if variableValue == "u":
            return "u"
        elif variableValue == 0:
            return 1
        else:
            return 0
    else:
        if variableValue == "u":
            return "u"
        elif variableValue == 1:
            return 1
        else:
            return 0


def clauseStatus(clause):
    # print("CLAUSE STATUS")
    refA = litValue(clause[0], variableVals[abs(clause[0])-1])
    # print(clause[0])
    # print(clause[1])
    if clause[1] == 0 and variableVals[abs(clause[0])-1] =="u":
        # print("UNIT")
        return "UNIT"
    refB = litValue(clause[1], variableVals[abs(clause[1])-1])
    if refA == 1 or refB == 1:
        # print("SATISIFIED")
        return "SATISFIED"
    elif refA == 0 and refB == 0:
        # print("UNSAT")
        return "UNSATISFIED"
    elif (refA == "u" or refB == "u") and refA != refB:
        # print("UNIT")
        return "UNIT"
    else:
        # print("UNRES")
        return "UNRESOLVED"

def numLitInClauseWithDL(clause, dl):
    count = 0
    min = copy.deepcopy(dl)
    for x in clause:
        if variableDecisionLevels[abs(x)-1] == dl:
            count += 1
        if variableDecisionLevels[abs(x)-1] < min and x!=0:
            min = variableDecisionLevels[abs(x)-1]
    return [count, min]

def resolution(list1, list2):
    l1 = copy.deepcopy(list1)
    l2 = copy.deepcopy(list2)
    for x in list1:
        if -x in list2 and -x != 0:
            l2.remove(-x)
            l1.remove(x)
        if x in list2:
            l2.remove(x)
    return(l1+l2)

def conflictAnalysis(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, maxDL):
    # print("CONFLICT ANALYSIS")
    previousIntermediate = copy.deepcopy(variableAntecedents[nbvar])
    nextIntermediate = []
    i = maxDL
    loopBool = True
    while loopBool:
        pcPreviousIntermediate = copy.deepcopy(previousIntermediate)
        for literal in pcPreviousIntermediate:
            if variableDecisionLevels[abs(literal)-1] == maxDL and variableAntecedents[abs(literal)-1] != None:
#                print(clauses[variableAntecedents[abs(literal)-1]])
                nextIntermediate = resolution(previousIntermediate, clauses[variableAntecedents[abs(literal)-1]-1])
                if nextIntermediate == previousIntermediate:
                    loopBool = False
                previousIntermediate = copy.deepcopy(nextIntermediate)
    return nextIntermediate

def conflictAnalysisUIP(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel):
    # print("CONFLICT ANALYSIS")
    previousIntermediate = copy.deepcopy(variableAntecedents[nbvar])
    nextIntermediate = copy.deepcopy(variableAntecedents[nbvar])
    loopBool = True
    while loopBool:
        # print(variableAntecedents[nbvar])
        for x in variableAntecedents[nbvar]:
            pcPreviousIntermediate = copy.deepcopy(previousIntermediate)
            numberOfLiteralsInClauseWithDL = numLitInClauseWithDL(previousIntermediate, decisionLevel)
            # print("NUMBER OF LITERALS IN CLAUSES WITH DECISION LEVEL: " + str(decisionLevel))
            # print(numberOfLiteralsInClauseWithDL)
            if numberOfLiteralsInClauseWithDL[0] == 1:
                loopBool = False
                # print("PREVIOUS INTERMEDIATE AND MINIMUM DECISION LEVEL IN CLAUSE")
                # print([previousIntermediate, numberOfLiteralsInClauseWithDL[1]])
                return ([previousIntermediate, numberOfLiteralsInClauseWithDL[1]])
            else:
                # print("ELSE")
                # print(pcPreviousIntermediate)
                for literal in pcPreviousIntermediate:
                    # print(literal)
                    # print(variableDecisionLevels[abs(literal)-1])
                    if variableDecisionLevels[abs(literal)-1] == decisionLevel and variableAntecedents[abs(literal)-1] != None and literal != 0:
                        nextIntermediate = resolution(previousIntermediate, clauses[variableAntecedents[abs(literal)-1]])
                        # print("RESOLVE CLAUSES: ")
                        # print(previousIntermediate)
                        # print(clauses[variableAntecedents[abs(literal)-1]])
                        # print("RESOLVED CLAUSE: ")
                        # print(nextIntermediate)
                    if nextIntermediate == previousIntermediate:
                        loopBool = False
                    previousIntermediate = copy.deepcopy(nextIntermediate)
    dls = []
    for x in nextIntermediate:
        level = variableDecisionLevels[abs(x)-1]
        if level != -1:
            dls.append(level)
    decisionLevel = min(dls)
    return [nextIntermediate, decisionLevel]



def unitPropCDCL(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel):
    # print("UNIT PROPAGATION STEP")
    clauseCopy = copy.deepcopy(clauses)
    numOfUnitClauses = 1
    while numOfUnitClauses > 0:
        numOfUnitClauses = 0
        for clause in clauses:
            clstatus = clauseStatus(clause)
            # print(clstatus)
            # print(clause)
            if clstatus == "UNSATISFIED":
                variableAntecedents[nbvar] = clause
#                print(conflictAnalysis(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel))
                return False
            elif clstatus == "UNIT":
                numOfUnitClauses += 1
                if clause[0] < 0 and variableVals [abs(clause[0])-1] == "u":
                    variableAntecedents[abs(clause[0])-1] = clauses.index(clause)
                    variableVals[abs(clause[0])-1] = 0
                    unassignedVariables.remove(abs(clause[0]))
#                    dl = [variableDecisionLevels[x-1] for x in clause if x != clause[0] and x != 0]
#                    dl.append(0)
#                    dl = max(dl)
                    updateWatchedLits(watchedLiterals, 0, clause[0])
                    variableDecisionLevels[abs(clause[0])-1] = decisionLevel
                elif clause[0] > 0 and variableVals[abs(clause[0])-1] == "u":
                    variableAntecedents[abs(clause[0])-1] = clauses.index(clause)
                    variableVals[abs(clause[0])-1] = 1
                    unassignedVariables.remove(abs(clause[0]))
                    updateWatchedLits(watchedLiterals, 1, clause[0])
#                    dl = [variableDecisionLevels[x] for x in clause if x != clause[0]]
#                    dl.append(0)
#                    dl = max(dl)
                    variableDecisionLevels[abs(clause[0])-1] = decisionLevel
                elif clause[1] < 0:
                    variableAntecedents[abs(clause[1])-1] = clauses.index(clause)
                    variableVals[abs(clause[1])-1] = 0
                    unassignedVariables.remove(abs(clause[1]))
                    updateWatchedLits(watchedLiterals, 0, clause[1])
#                    dl = [variableDecisionLevels[x] for x in clause if x != clause[1]]
#                    dl.append(0)
#                    dl = max(dl)
                    variableDecisionLevels[abs(clause[1])-1] = decisionLevel
                else:
                    variableAntecedents[abs(clause[1])-1] = clauses.index(clause)
                    variableVals[abs(clause[1])-1] = 1
                    unassignedVariables.remove(abs(clause[1]))
                    updateWatchedLits(watchedLiterals, 1, clause[1])
#                    dl = [variableDecisionLevels[x] for x in clause if x != clause[1]]
#                    dl.append(0)
#                    dl = max(dl)
                    variableDecisionLevels[abs(clause[1])-1] = decisionLevel
                # print("ANTECEDENTS")
                # print(variableAntecedents)
                # print("DECISION LEVELS")
                # print(variableDecisionLevels)
                # print("VARIABLE VALS")
                # print(variableVals)


def backtrack(conflictAnalysis, variableVals, variableAntecedents, variableDecisionLevels, unassignedVariables, watchedLiterals):
    # print("\n\nBACKTRACK")
    # print(clauses)
    # print(conflictAnalysis)
    backtrackVar = 0
    backtrackVarVal = 0
    for variableDL in range (0, len(variableDecisionLevels)):
        if variableDecisionLevels[variableDL] > conflictAnalysis[1]:
            variableVals[variableDL] = "u"
            variableAntecedents[variableDL] = None
            variableDecisionLevels[variableDL] = -1
            unassignedVariables.append(variableDL + 1)
        elif variableDecisionLevels[variableDL] == conflictAnalysis[1] and variableAntecedents[variableDL] != None:
            variableVals[variableDL] = "u"
            variableAntecedents[variableDL] = None
            variableDecisionLevels[variableDL] = -1
            unassignedVariables.append(variableDL + 1)
        elif variableDecisionLevels[variableDL] == conflictAnalysis[1] and variableAntecedents[variableDL] == None:
            variableVals[variableDL] = (variableVals[variableDL] + 1) % 2
            # variableAntecedents[variableDL] = None
            backtrackVar = variableDL + 1
            backtrackVarVal = variableVals[variableDL]
    updateWatchedLits(watchedLiterals, literal = backtrackVar, variableValue=backtrackVarVal)
    # print(watchedLiterals)
    # print(variableAntecedents)
    # print(variableDecisionLevels)
    # print(variableVals)




"""
    CDCL(φ, ν)
    if (UnitPropagation(φ, ν ) == CONFLICT)
    then return UNSAT
    dl ← 0                                                      Decision level
    while (not AllVariablesAssigned(φ, ν ))
    do (x, v) = PickBranchingVariable(φ, ν)
    dl ← dl + 1                                             Increment decision level due to new decision
    ν ← ν ∪ {(x, v)}
    if (UnitPropagation(φ, ν) == CONFLICT)
    then β = ConflictAnalysis(φ, ν)
    if (β < 0)                                      Diagnose stage
    then return UNSAT
    else Backtrack(φ, ν, β)
    dl ← β                                  Decrement decision level due to backtracking
    return SAT
    """


def clauseLearningSATsolver(nbclause, nbvar, listOfVariables, literals, clauses, variableVals, variableAntecedents, variableDecisionLevels):
    decisionLevel = 0
    watchedLiterals = createWatchedLits(clauses, nbvar)
#    print(watchedLiterals)
#    for x in watchedLiterals:
#        for y in x[0]:
#            print(clauses[y])
#        for y in x[1]:
#            print(clauses[y])
#    for x in watchedLiterals[1]:
#        for y in x[0]:
#            print(clauses[y])
#        for y in x[1]:
#            print(clauses[y])
#    variableVals = ["u" for x in range(nbvar)]
#    variableAntecedents = [None for x in range(nbvar + 1)]
#    variableDecisionLevels = [-1 for x in range(nbvar)]
    unassignedVariables = copy.deepcopy(listOfVariables)

#--  Deciding variable and its value
    if isinstance(unitPropCDCL(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause,
                               unassignedVariables, watchedLiterals, decisionLevel), (bool)):
        return False
    while(len(unassignedVariables) != 0):
        literal = getNewLiteral(unassignedVariables, literals, nbvar)
        # print(variableAntecedents)
        decisionLevel += 1
        value = randint(0, 1)
        variableVals[literal-1] = value
        unassignedVariables.remove(literal)
        variableDecisionLevels[literal-1] = decisionLevel
        # print("\n NEW DECISION \n")

#        print(literal)
#        print(variableVals)
#        print(variableDecisionLevels)
#        print(variableAntecedents)
        updateWatchedLits(watchedLiterals, value, literal)
        if isinstance(unitPropCDCL(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel), (bool)):
#            print(literal)
#            print(variableVals)
#            print(variableDecisionLevels)
#            print(variableAntecedents)
            conflictAnalysis = conflictAnalysisUIP(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel)
            clauses.append(conflictAnalysis[0])
            watchedLitsAdd(watchedLiterals, conflictAnalysis[0], len(clauses))
            backtrackLevel = conflictAnalysis[1]
            if backtrackLevel < 0:
                return False
            else:
                backtrack(conflictAnalysis, variableVals, variableAntecedents, variableDecisionLevels, unassignedVariables, watchedLiterals)
                decisionLevel = backtrackLevel
    return ["SAT", variableVals]

#------------------------------------


#print(testSatisfiableWithLiterals(nbvar, z, clauses))


#------------------------- TESTING -------------------------#

#nbvar = 8
#clauses = [[1, 8, -2, 0], [1,-3,0], [2, 3, 4, 0], [-4,-5,0], [7,-4,-6,0], [5,6,0]]
#variableVals = [0, 0, 0, 1, 0, 0, 0, 0]
#variableAntecedents =  [None, 1, 2, 3, 4, 5, None, None, [5,6,0]]
#variableDecisionLevels = [5, 5, 5, 5, 5, 5, 2, 3]



listOfVariables = untestedLiterals
variableVals = ["u" for x in range(nbvar)]
variableAntecedents = [None for x in range(nbvar+1)]
variableDecisionLevels = [-1 for x in range(nbvar)]
watchedLiterals =[[[],[]] for x in range(nbvar)]
unassignedVariables = untestedLiterals
untestedLiterals = [x for x in range(1, nbvar+1)]



watchedLiterals = createWatchedLits(clauses, nbvar)
# print("ANSWER")
# #print(conflictAnalysisUIP(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, 5))
# #unitPropCDCL(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, 5)
# print(variableVals)
# print(variableAntecedents)
# print(variableDecisionLevels)
# #print(resolution([1,2,3],[-1,2,-3]))
# print("------------------------")

#
results = clauseLearningSATsolver(nbclause, nbvar, listOfVariables, literals, clauses, variableVals, variableAntecedents, variableDecisionLevels)
print("TEST")
print(results)
print(testSatisfiableWithLiterals(nbvar, results[1], clauses))


# print("BREAK")
# print(data[2])


