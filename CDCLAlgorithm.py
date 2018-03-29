import parseDataFile
import sys
from random import randint
import copy


#Parse data file
file = str(sys.argv[1])
print(file)
data = parseDataFile.parseDataFile(file)
nbvar = data[0]
nbclause = data[1]
clauses = copy.deepcopy(data[2])



def getNewLiteral(untestedLiterals, literals, nbvar):
    if len(untestedLiterals) > 1:
        x = randint(0, len(untestedLiterals)-1)
        literal = untestedLiterals[x]
        return literal
    elif len(untestedLiterals) == 1:
        literal = untestedLiterals[0]
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

literals = []
untestedLiterals = [x for x in range(1, nbvar+1)]
listOfVariables = untestedLiterals
variableVals = ["u" for x in range(nbvar)]
variableAntecedents = [None for x in range(nbvar+1)]
variableDecisionLevels = [-1 for x in range(nbvar)]
watchedLiterals =[[[],[]] for x in range(nbvar)]
unassignedVariables = untestedLiterals






def createWatchedLits(clauses, nbvar):
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
    if variableValue ==1:
        clauseNumber = copy.deepcopy(watchedLiterals[abs(literal)-1][0])
        for x in clauseNumber:
            clause = clauses[x]
            if clause[0] == -abs(literal):
                previousIndex = 0
            elif clause[1] == -abs(literal):
                previousIndex = 1
            else:
                previousIndex = 2;
            swapped = False
            if previousIndex <= 1:
                for y in range(2, len(clause)):
                    if not swapped:
                        if ((variableVals[abs(clause[y])-1] == "u" or litValue(clause[y], variableVals[abs(clause[y])-1]) == 1)) and clause[y]!=0:
                            swapped = True
                            watchedLiterals[abs(literal)-1][0].remove(x)
                            if clause[y] < 0:
                                watchedLiterals[abs(clause[y])-1][0].append(x)
                            else:
                                watchedLiterals[abs(clause[y])-1][1].append(x)
                            print("SWAP")
                            print(clause)
                            temp1 = copy.deepcopy(clause[y])
                            temp2 = copy.deepcopy(clause[previousIndex])
                            clause[y] = temp2
                            clause[previousIndex]= temp1
                            print(clause)
    elif variableValue == 0:
        watchedLitsCopy = copy.deepcopy(watchedLiterals[abs(literal)-1][1])
        for clauseNum in watchedLitsCopy:
            clause = clauses[clauseNum]
            swapped = False
            print(clause)
            previousIndex = clause.index(abs(literal))
            if previousIndex <= 1:
                for x in range(2, len(clause)):
                    if not swapped:
                        if ((variableVals[abs(clause[x])-1] == "u" or litValue(clause[x], variableVals[abs(clause[x])-1]) == 1)) and clause[x]!=0:
                            swapped = True
                            watchedLiterals[abs(literal)-1][1].remove(clauseNum)
                            if clause[x] < 0:
                                watchedLiterals[abs(clause[x])-1][0].append(clauseNum)
                                temp1 = copy.deepcopy(clause[x])
                                temp2 = copy.deepcopy(clause[previousIndex])
                                clause[x] = temp2
                                clause[previousIndex] = temp1
                            else:
                                watchedLiterals[abs(clause[x])-1][1].append(clauseNum)
                                temp1 = copy.deepcopy(clause[x])
                                temp2 = copy.deepcopy(clause[previousIndex])
                                clause[x] = temp2
                                clause[previousIndex] = temp1
    elif variableValue == "u":
        for clause in clauses:
            if literal in clause or -literal in clause:
                print(clause)
                if litValue(clause[0], variableVals[abs(clause[0])-1]) == 0:
                    print("H")
                    temp = clause[0]
                    didSwap = False
                    if literal in clause and clause.index(literal) > 1:
                        clause[clause.index(literal)] = clause[0]
                        clause[0] = literal
                        didSwap= True
                        watchedLiterals[literal - 1][1].append(clauses.index(clause))
                    elif -literal in clause and clause.index(-literal) > 1:
                        clause[clause.index(-literal)] = clause[0]
                        clause[0] = -literal
                        watchedLiterals[literal - 1][0].append(clauses.index(clause))
                        didSwap=True
                    if temp < 0 and didSwap:
                        for j in watchedLiterals[abs(temp)-1][0]:
                            print(clauses[j])
                            print(j)
                        watchedLiterals[abs(temp) - 1][0].remove(clauses.index(clause))

                    elif temp >=0 and didSwap:
                        for j in watchedLiterals[abs(temp)-1][1]:
                            print(clauses[j])
                            print(j)
                        watchedLiterals[abs(temp) - 1][1].remove(clauses.index(clause))

                elif litValue(clause[1], variableVals[abs(clause[1])-1]) == 0:
                    print("K")
                    temp = clause[1]
                    didSwap = False
                    if literal in clause and clause.index(literal) > 1:
                        clause[clause.index(literal)] = clause[1]
                        clause[1] = literal
                        watchedLiterals[abs(literal) - 1][1].append(clauses.index(clause))
                        didSwap = True
                    elif -literal in clause and clause.index(-literal) > 1:
                        clause[clause.index(-literal)] = clause[1]
                        clause[1] = -literal
                        watchedLiterals[abs(literal) - 1][0].append(clauses.index(clause))
                        didSwap = True
                    if temp < 0 and didSwap:
                        for j in watchedLiterals[abs(temp)-1][0]:
                            print(clauses[j])
                        watchedLiterals[abs(temp) - 1][0].remove(clauses.index(clause))

                    elif temp > 0 and didSwap:
                        for j in watchedLiterals[abs(temp)-1][1]:
                            print(clauses[j])
                        watchedLiterals[abs(temp) - 1][1].remove(clauses.index(clause))

        print("\n" + literal.__str__())
        clausesWithLit = filter(lambda x: literal in x or -literal in x, clauses)
        for c in clausesWithLit:
            print(c)
            for vari in c:
                print(variableVals[abs(vari)-1])






def watchedLitsAdd(watchedLiterals, clause, numOfClause):
    clause.remove(0)
    clause.append(0)
    if clause[0] < 0:
        watchedLiterals[abs(clause[0])-1][0].append(numOfClause -1)
    elif clause[0] > 0:
        watchedLiterals[abs(clause[0])-1][1].append(numOfClause -1)
    if clause[1] < 0:
        watchedLiterals[abs(clause[1])-1][0].append(numOfClause -1)
    elif clause[1] > 0:
        watchedLiterals[abs(clause[1])-1][1].append(numOfClause -1)




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
    refA = litValue(clause[0], variableVals[abs(clause[0])-1])
    if clause[1] == 0 and variableVals[abs(clause[0])-1] =="u":
        return "UNIT"
    refB = litValue(clause[1], variableVals[abs(clause[1])-1])
    if refA == 1 or refB == 1:
        return "SATISFIED"
    elif ((refA == 0 and refB == 0) or (refA == 0 and clause[1]==0) or (refB == 0 and clause[0] == 0)):
        return "UNSATISFIED"
    elif (refA == "u" or refB == "u") and refA != refB:
        return "UNIT"
    else:
        return "UNRESOLVED"



def numLitInClauseWithDL(clause, dl):
    count = 0
    max = 0
    for x in clause:
        if variableDecisionLevels[abs(x)-1] == dl and x!=0:
            count += 1
        if variableDecisionLevels[abs(x)-1] > max and x!=0 and variableDecisionLevels[abs(x)-1] != dl:
            max = variableDecisionLevels[abs(x)-1]
    return [count, max]




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





def conflictAnalysisUIP(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel):
    previousIntermediate = copy.deepcopy(variableAntecedents[nbvar])
    nextIntermediate = copy.deepcopy(variableAntecedents[nbvar])
    loopBool = True
    while loopBool:
        pcPreviousIntermediate = copy.deepcopy(previousIntermediate)
        numberOfLiteralsInClauseWithDL = numLitInClauseWithDL(previousIntermediate, decisionLevel)
        if numberOfLiteralsInClauseWithDL[0] == 1:
            nextIntermediate = previousIntermediate
            loopBool = False
            for x in range(0, len(nextIntermediate)):
                if variableDecisionLevels[abs(nextIntermediate[x]) - 1] == decisionLevel:
                    temp = nextIntermediate[0]
                    nextIntermediate[0] = nextIntermediate[x]
                    nextIntermediate[x] = temp
            dls = []
            for x in nextIntermediate:
                if x != 0:
                    level = variableDecisionLevels[abs(x) - 1]
                    if level != decisionLevel:
                        dls.append(level)
                print("CHECK THiS")
                print(dls)
            if len(dls) == 0:
                dls.append(-1)
            decisionLevel = max(dls)
            return ([nextIntermediate, decisionLevel])
        else:
            loopBool = True
            print(pcPreviousIntermediate)
            for literal in pcPreviousIntermediate:
                if variableDecisionLevels[abs(literal)-1] == decisionLevel and variableAntecedents[abs(literal)-1] != None and literal != 0:
                    print(literal)
                    print(clauses[variableAntecedents[abs(literal)-1]])
                    print("clause above decision lev")
                    for vari in clauses[variableAntecedents[abs(literal)-1]]:
                        print(variableDecisionLevels[abs(vari)-1])
                    nextIntermediate = resolution(nextIntermediate, clauses[variableAntecedents[abs(literal)-1]])
                    print(nextIntermediate)
                    for vari in nextIntermediate:
                        print(variableDecisionLevels[abs(vari)-1])
                if numLitInClauseWithDL(nextIntermediate, decisionLevel) == 1:
                    previousIntermediate = copy.deepcopy(nextIntermediate)
                    loopBool = False
                    break
            if set(nextIntermediate) == set(previousIntermediate):
                print("SAME")
                loopBool = False
            previousIntermediate = copy.deepcopy(nextIntermediate)
    dls = []
    for x in nextIntermediate:
        if x != 0:
            level = variableDecisionLevels[abs(x)-1]
            if level != decisionLevel:
                dls.append(level)
        print("CHECK THiS")
        print(dls)
    if len(dls) == 0:
        dls.append(-1)
    for x in range(0, len(nextIntermediate)):
        if variableDecisionLevels[abs(nextIntermediate[x])-1] == decisionLevel:
            temp = nextIntermediate[0]
            nextIntermediate[0] = nextIntermediate[x]
            nextIntermediate[x] = temp
    decisionLevel = max(dls)
    return [nextIntermediate, decisionLevel]





def unitPropCDCL(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel):
    clauseCopy = copy.deepcopy(clauses)
    numOfUnitClauses = 1
    while numOfUnitClauses > 0:
        numOfUnitClauses = 0
        for clause in clauses:
            clstatus = clauseStatus(clause)
            if clstatus == "UNSATISFIED":
                variableAntecedents[nbvar] = clause
                return False
            elif clstatus == "UNIT":
                print("UNIT PROP")
                print(clauses.index(clause))
                print(len(clauses))
                print(clause)
                for vari in clause:
                    print(variableDecisionLevels[abs(vari) - 1])
                numOfUnitClauses += 1
                if clause[0] < 0 and variableVals [abs(clause[0])-1] == "u":
                    variableAntecedents[abs(clause[0])-1] = clauses.index(clause)
                    variableVals[abs(clause[0])-1] = 0
                    unassignedVariables.remove(abs(clause[0]))
                    updateWatchedLits(watchedLiterals, 0, clause[0])
                    variableDecisionLevels[abs(clause[0])-1] = decisionLevel
                elif clause[0] > 0 and variableVals[abs(clause[0])-1] == "u":
                    variableAntecedents[abs(clause[0])-1] = clauses.index(clause)
                    variableVals[abs(clause[0])-1] = 1
                    unassignedVariables.remove(abs(clause[0]))
                    updateWatchedLits(watchedLiterals, 1, clause[0])
                    variableDecisionLevels[abs(clause[0])-1] = decisionLevel
                elif clause[1] < 0 and variableVals[abs(clause[1])-1] == "u":
                    variableAntecedents[abs(clause[1])-1] = clauses.index(clause)
                    variableVals[abs(clause[1])-1] = 0
                    unassignedVariables.remove(abs(clause[1]))
                    updateWatchedLits(watchedLiterals, 0, clause[1])
                    variableDecisionLevels[abs(clause[1])-1] = decisionLevel
                elif clause[1] > 0 and variableVals[abs(clause[1])-1] == "u":
                    variableAntecedents[abs(clause[1])-1] = clauses.index(clause)
                    variableVals[abs(clause[1])-1] = 1
                    unassignedVariables.remove(abs(clause[1]))
                    updateWatchedLits(watchedLiterals, 1, clause[1])
                    variableDecisionLevels[abs(clause[1])-1] = decisionLevel






def backtrack(conflictAnalysis, variableVals, variableAntecedents, variableDecisionLevels, unassignedVariables, watchedLiterals, clauses):
    backtrackVar = 0
    backtrackVarVal = 0
    print("backtrack level")
    print(conflictAnalysis[1])
    for variableDL in range (0, len(variableDecisionLevels)):
        if variableDecisionLevels[variableDL] > conflictAnalysis[1]:
            variableVals[variableDL] = "u"
            variableAntecedents[variableDL] = None
            variableDecisionLevels[variableDL] = -1
            unassignedVariables.append(variableDL + 1)
            updateWatchedLits(watchedLiterals, literal=variableDL+1, variableValue="u")
        # elif variableDecisionLevels[variableDL] == conflictAnalysis[1] and variableAntecedents[variableDL] != None:
        #     variableVals[variableDL] = "u"
        #     variableAntecedents[variableDL] = None
        #     variableDecisionLevels[variableDL] = -1
        #     unassignedVariables.append(variableDL + 1)
        # elif variableDecisionLevels[variableDL] == conflictAnalysis[1] and variableAntecedents[variableDL] == None:
        #     # variableVals[variableDL] = (variableVals[variableDL] + 1) % 2
        #     backtrackVar = variableDL + 1
        #     backtrackVarVal = variableVals[variableDL]
    updateWatchedLits(watchedLiterals, literal = backtrackVar, variableValue=backtrackVarVal)











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
    unassignedVariables = copy.deepcopy(listOfVariables)
    if isinstance(unitPropCDCL(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause,
                               unassignedVariables, watchedLiterals, decisionLevel), (bool)):
        return False
    conflict = False
    while(len(unassignedVariables) != 0):
        print("stu")
        if not conflict:
            literal = getNewLiteral(unassignedVariables, literals, nbvar)
            print(literal)
            decisionLevel += 1
            print(decisionLevel)
            value = randint(0, 1)
            print(value)
            variableVals[literal-1] = value
            unassignedVariables.remove(literal)
            variableDecisionLevels[literal-1] = decisionLevel
            updateWatchedLits(watchedLiterals, value, literal)
        if isinstance(unitPropCDCL(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel), (bool)):
            conflictAnalysis = conflictAnalysisUIP(clauses, variableVals, variableAntecedents, variableDecisionLevels, nbvar, nbclause, unassignedVariables, watchedLiterals, decisionLevel)
            clauses.append(conflictAnalysis[0])
            watchedLitsAdd(watchedLiterals, conflictAnalysis[0], len(clauses))
            backtrackLevel = conflictAnalysis[1]
            print(conflictAnalysis[0])
            print("These are the values")
            for x in conflictAnalysis[0]:
                print(variableVals[abs(x)-1])
            print("These are the decisions")
            for x in conflictAnalysis[0]:
                print(variableDecisionLevels[abs(x) - 1])
            print("\n")
            if backtrackLevel < 0:
                return False
            else:
                backtrack(conflictAnalysis, variableVals, variableAntecedents, variableDecisionLevels, unassignedVariables, watchedLiterals, clauses)
                decisionLevel = backtrackLevel
            print(conflictAnalysis[0])
            print("These are the values after backtracking")
            for x in conflictAnalysis[0]:
                print(variableVals[abs(x) - 1])
            print("These are the decisions after backtracking")
            for x in conflictAnalysis[0]:
                print(variableDecisionLevels[abs(x) - 1])
            print("\n")
            conflict = True
        else:
            conflict = False
    return ["SAT", variableVals]






listOfVariables = untestedLiterals
variableVals = ["u" for x in range(nbvar)]
variableAntecedents = [None for x in range(nbvar+1)]
variableDecisionLevels = [-1 for x in range(nbvar)]
watchedLiterals =[[[],[]] for x in range(nbvar)]
unassignedVariables = untestedLiterals
untestedLiterals = [x for x in range(1, nbvar+1)]



watchedLiterals = createWatchedLits(clauses, nbvar)



results = clauseLearningSATsolver(nbclause, nbvar, listOfVariables, literals, clauses, variableVals, variableAntecedents, variableDecisionLevels)
print("TEST")
print(results)
print(testSatisfiableWithLiterals(nbvar, results[1], clauses))



