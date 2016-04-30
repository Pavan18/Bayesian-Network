from decimal import Decimal
import sys
import copy
import itertools
import re

#Class to parse the input file
class ReadFromFile:
    bayesianNW = {}
    inputQuery = []
    sortedVars = []

    def sortInputVars(self, networkDictionary):
        var = networkDictionary.keys()
        l = []
        while len(l) < len(var):
            for v in var:
                if v not in l and all(x in l for x in networkDictionary[v]['Parents']):
                    l.append(v)
        return l


    def addCondProbs(self, vars, cpvalues):
        self.bayesianNW[vars.strip('\n')]['Conditional_Prob'] = cpvalues
        return

    def addProbs(self, vars, probvals):
        self.bayesianNW[vars.strip('\n')]['Probability'] = probvals
        return

    def countSep(self, fileString):
        return fileString.count('|')

    def addParent(self, c, pars):
        self.bayesianNW[c.strip('\n')]['Parents'] = pars
        return



    def getQuery(self):
        return self.inputQuery

    def getSortedVars(self):
        return self.sortedVars

    def addChildren(self, p, c):
        self.bayesianNW[p.strip('\n')]['Children'] = c
        return


    def addVars(self, vars, typevals):
        self.bayesianNW[vars.strip('\n')]['Type'] = typevals
        return

    def getBayesianNW(self):
        return self.bayesianNW

    def readInputFile(self, FileName):
        filePointer = open(FileName)
        curr = filePointer.readline().strip()
        i = 0
        while curr[0] != '*':
            self.inputQuery.append(curr)
            curr = filePointer.readline().strip()

        currentLine = filePointer.readline().strip()
        while currentLine != '':
            prev = currentLine
            countSeps = self.countSep(prev)
            if countSeps == 0:
                var_decision = filePointer.readline().strip()
                if var_decision[0] == 'd':

                    self.bayesianNW[prev.strip('\n')] = {'Parents': [], 'Probability': var_decision.strip('\n'),
                                                         'Conditional_Prob': [], 'Type': 'Decision'}
                    self.addChildren(prev, [])
                else:
                    self.bayesianNW[prev.strip('\n')] = {'Parents': [], 'Probability': var_decision.strip('\n'),
                                                         'Conditional_Prob': [], 'Type': 'Normal'}
                    self.addChildren(prev, [])

            else:
                prev_Split = prev.split(' | ')
                parents_Line = prev_Split[1].split(' ')
                for i in range(0, len(parents_Line)):
                    self.bayesianNW[parents_Line[i]]['Children'].append(prev_Split[0].strip())

                self.bayesianNW[prev_Split[0].strip('\n')] = {}
                self.addParent(prev_Split[0], parents_Line)
                self.addChildren(prev_Split[0], [])
                scenario_prob = {}
                for i in range(0, pow(2, len(parents_Line))):
                    condprob = filePointer.readline().strip()
                    splitcondprob = condprob.split(' ')
                    prob = splitcondprob[0]
                    truthVal = splitcondprob[1:]
                    truth = tuple(True if x == '+' else False for x in truthVal)
                    scenario_prob[truth] = prob

                self.addCondProbs(prev_Split[0], scenario_prob)
                self.addProbs(prev_Split[0], [])
                self.addVars(prev_Split[0], 'Normal')
            currentLine = filePointer.readline()
            currentLine = filePointer.readline().strip()
        TopoSortedVars = self.sortInputVars(self.bayesianNW)
        return TopoSortedVars

#Class to create Bayesian Network
class bayesianNet:
    InputParser = ReadFromFile()
    BayesNet = {}
    QueriesList = []
    SortedVars = []

    def InitNetwork(self,fileName):
        self.SortedVars=self.InputParser.readInputFile(fileName)
        self.BayesNet = self.InputParser.getBayesianNW()
        self.QueriesList = self.InputParser.getQuery()

    def getSelectedNodes(self, sortedVariables, networkDictionary, observedVariables):
        x = observedVariables.keys()
        newNetwork = []

        bnPresence = [True if a in x else False for a in sortedVariables]

        for i in range(0, pow(len(sortedVariables), 2)):
            for v in sortedVariables:
                if bnPresence[sortedVariables.index(v)] != True and any(
                                bnPresence[sortedVariables.index(c)] == True for c in networkDictionary[v]['Children']):
                    index = sortedVariables.index(v)
                    bnPresence[index] = True

        for eachNode in sortedVariables:
            if bnPresence[sortedVariables.index(eachNode)] == True:
                newNetwork.append(eachNode)

        return newNetwork

    def getProbabilityQueryType(self, query):
        return query[0]

    def getProbability_var(self, Y, e):

        if self.BayesNet[Y]['Type'] == 'Decision':
            return 1.0

        if len(self.BayesNet[Y]['Parents']) == 0:
            if e[Y] == True:
                prob = float(self.BayesNet[Y]['Probability'])
                return float(self.BayesNet[Y]['Probability'])
            else:
                return 1.0-float(self.BayesNet[Y]['Probability'])
        else:

            parents = tuple(e[p] for p in self.BayesNet[Y]['Parents'])

            # query for prob of Y = y
            if e[Y] == True:
                return float(self.BayesNet[Y]['Conditional_Prob'][parents])
            else:
                return 1.0-float(self.BayesNet[Y]['Conditional_Prob'][parents])

    def enumAll(self,X, vars, e):
        if not vars:
            return 1.0
        Y = vars[0]
        if Y in e:
            returnValue = self.getProbability_var(Y, e) * self.enumAll(X, vars[1:], e)
        else:
            prob = []
            e2 = copy.deepcopy(e)
            for eachValue in [True, False]:
                e2[Y] = eachValue
                prob.append(self.getProbability_var(Y, e2) * self.enumAll(X,vars[1:], e2))
            returnValue = sum(prob)
        return returnValue

    def enumAsk(self):
        OutputWrite=WriteFile()
        OutputWrite.InitFileWriting()
        for i in range(0, len(self.QueriesList)):
            givenquery = self.QueriesList[i]
            if self.getProbabilityQueryType(givenquery) == 'P':
                splitgivenquery = givenquery.split('(')
                query_values = splitgivenquery[1]
                query_vars = 0
                Dictionary = {}
                evident_Dictionary = {}
                variables = []
                var_boolvalues = []
                X = ''
                flag = False

                if query_values.count('|') == 1:
                    flag = True
                    b = query_values[:query_values.index('|')]
                    if b.find(",") != -1:
                        b_split = b.split(", ")
                        for i in range(0, len(b_split)):
                            query_vars = query_vars + 1
                            b_split_rest = b_split[i][:b_split[i].index(' ')]
                            variables.append(b_split_rest)
                            if b_split[i].find('+') != -1:
                                var_boolvalues.append(True)
                            else:
                                var_boolvalues.append((False))
                    else:
                        query_vars = 1
                        X = b[:b.index(' ')]
                        variables.append(X)
                        if b.find('+') != -1:
                            var_boolvalues.append(True)
                        else:
                            var_boolvalues.append(False)
                    d = query_values[query_values.index('| ') + 2:]
                else:
                    d = query_values
                e = d.split(', ')

                for i in range(0, len(e)):
                    variables.append((e[i][:e[i].index(' =')]))
                    if e[i].find('+') != -1:
                        var_boolvalues.append(True)
                    else:
                        var_boolvalues.append(False)
                for i in range(0, len(variables)):
                    Dictionary[variables[i]] = var_boolvalues[i]

                bn = self.getSelectedNodes(self.SortedVars, self.BayesNet,Dictionary)
                Prob = self.enumAll(X, bn, Dictionary)

                if flag == True:
                    X2 = ''
                    evidenceValue = var_boolvalues[query_vars:]
                    evidenceVariables = variables[query_vars:]
                    for i in range(0, len(evidenceVariables)):
                        evident_Dictionary[evidenceVariables[i]] = evidenceValue[i]
                    evidenceBN = self.getSelectedNodes(self.SortedVars, self.BayesNet, Dictionary)
                    quotient = self.enumAll(X2, evidenceBN, evident_Dictionary)
                    opResult = Decimal(str(Prob / quotient)).quantize(Decimal('.01'))
                    #print(opResult) ----
                    OutputWrite.WriteFile(str(opResult))
                else:
                    opResult = Decimal(str(Prob)).quantize(Decimal('.01'))
                    #print(opResult) ----
                    OutputWrite.WriteFile(str(opResult))

            elif self.getProbabilityQueryType(givenquery) == 'E':
                splitgivenquery = givenquery.split('(')
                query_values = splitgivenquery[1]
                query_vars = 0
                Dictionary = {}
                evident_Dictionary = {}
                variables = []
                var_boolvalues = []
                X = ''
                flag = False
                variables.append('utility')
                var_boolvalues.append(True)
                if query_values.count('|') == 1:
                    flag = True
                    b = query_values[:query_values.index('|')]
                    if b.find(",") != -1:
                        b_split = b.split(", ")
                        for i in range(0, len(b_split)):
                            query_vars = query_vars + 1
                            b_split_rest = b_split[i][:b_split[i].index(' ')]
                            variables.append(b_split_rest)
                            if b_split[i].find('+') != -1:
                                var_boolvalues.append(True)
                            else:
                                var_boolvalues.append((False))
                    else:
                        query_vars = 1
                        X = b[:b.index(' ')]
                        variables.append(X)
                        if b.find('+') != -1:
                            var_boolvalues.append(True)
                        else:
                            var_boolvalues.append(False)
                    d = query_values[query_values.index('| ') + 2:]
                else:
                    d = query_values
                e = d.split(', ')
                for i in range(0, len(e)):
                    variables.append((e[i][:e[i].index(' =')]))
                    if e[i].find('+') != -1:
                        var_boolvalues.append(True)
                    else:
                        var_boolvalues.append(False)
                for i in range(0, len(variables)):
                    Dictionary[variables[i]] = var_boolvalues[i]
                bn = self.getSelectedNodes(self.SortedVars, self.BayesNet,Dictionary)
                Prob = self.enumAll(X, bn, Dictionary)

                if flag == True:
                    X2 = ''
                    evidenceVariables = variables[query_vars:]
                    evidenceValue = var_boolvalues[query_vars:]
                    for i in range(0, len(evidenceVariables)):
                        evident_Dictionary[evidenceVariables[i]] = evidenceValue[i]
                    evidenceBN = self.getSelectedNodes(self.SortedVars, self.BayesNet, evident_Dictionary)
                    quotient = self.enumAll(X2, evidenceBN, evident_Dictionary)
                    opResult = Decimal(str(Prob / quotient)).quantize(
                        Decimal('.01'))
                    #print(int(round(opResult))) ----
                    OutputWrite.WriteFile(str(int(round(opResult))))
                else:
                    opResult = Decimal(str(Prob)).quantize(Decimal('.01'))
#                    print(int(round(opResult)))
                    OutputWrite.WriteFile(str(int(round(opResult))))

            elif self.getProbabilityQueryType(givenquery) == 'M':
                splitgivenquery = givenquery.split('(')
                queryfunction = splitgivenquery[0]
                query_values = splitgivenquery[1]

                MEU_vars = []
                query_vars = 0
                Dictionary = {}
                evident_Dictionary = {}
                variables = []
                var_boolvalues = []
                X = ''
                flag = False
                resultDictionary = {}
                variables.append('utility')
                var_boolvalues.append(True)
                if query_values.count('|') == 1:
                    flag = True
                    b = query_values[:query_values.index('|')]
                    if b.find(",") != -1:
                        b_split = b.split(", ")
                        for i in range(0, len(b_split)):
                            if b_split[i].find('=')!=0:
                                query_vars = query_vars + 1
                                variables.append(b_split[i][:b_split[i].index(' ')])
                                if b_split[i].find('+') != -1:
                                    var_boolvalues.append(True)
                                else:
                                    var_boolvalues.append((False))
                            else:
                                MEU_vars.append(b_split[i][:b_split[i].index(' ')])
                    else:

                        query_vars = 1
                        X = b[:b.index(' ')]
                        if b.find('=') != -1:
                            variables.append(X)
                            if b.find('+') != -1:
                                var_boolvalues.append(True)
                            else:
                                var_boolvalues.append(False)
                        else:
                            MEU_vars.append(X)

                    d = query_values[query_values.index('| ') + 2:]


                else:
                    d = query_values

                e = d.split(', ')

                for i in range(0, len(e)):
                    if e[i].find('=') != -1:
                        variables.append((e[i][:e[i].index(' =')]))
                        if e[i].find('+') != -1:
                            var_boolvalues.append(True)
                        else:
                            var_boolvalues.append(False)
                    else:
                        MEU_vars.append(e[i].strip(")"))

                for i in range(0, len(variables)):
                    Dictionary[variables[i]] = var_boolvalues[i]

                MEU_Length = len(MEU_vars)

                MEU_TruthValue = list(itertools.product([True, False], repeat=MEU_Length))

                for i in range(0, len(MEU_TruthValue)):
                    tempEvidence = copy.deepcopy(Dictionary)
                    meuValue = ''
                    j = 0
                    for each in MEU_vars:
                        tempEvidence[each] = MEU_TruthValue[i][j]
                        if MEU_TruthValue[i][j] == True:
                            meuValue = meuValue + '+ '
                        else:
                            meuValue = meuValue + '- '
                        j = j + 1

                    bn = self.getSelectedNodes(self.SortedVars, self.BayesNet,
                                               tempEvidence)

                    Prob = self.enumAll(X, bn, tempEvidence)

                    if flag == True:
                        X2 = ''
                        evidenceVariables = variables[query_vars:]
                        evidenceValue = var_boolvalues[query_vars:]
                        for i in range(0, len(evidenceVariables)):
                            evident_Dictionary[evidenceVariables[i]] = evidenceValue[i]
                        evidenceBN = self.getSelectedNodes(self.SortedVars, self.BayesNet, evident_Dictionary)

                        quotient = self.enumAll(X2, evidenceBN, evident_Dictionary)

                        opResult = Decimal(str(Prob / quotient)).quantize(
                            Decimal('.01'))


                    else:
                        opResult = Decimal(str(Prob)).quantize(Decimal('.01'))

                    resultDictionary[opResult] = meuValue



                answer = max(resultDictionary.keys())

                #print(resultDictionary[answer] + str(int(round(answer))))
                OutputWrite.WriteFile(resultDictionary[answer] + str(int(round(answer))))

#Class to write the output to a file
class WriteFile:

    def InitFileWriting(self):
        file=open("output.txt","w")
        file.close()

    def WriteFile(self,strOuput):
        file=open("output.txt","a")
        file.write(strOuput+"\n")
        file.close()


#Class to recieve command line args and load sample input
class load:
    BayeNetworkObj=bayesianNet()
    def Bootup(self):
        self.BayeNetworkObj.InitNetwork(sys.argv[-1])
        self.BayeNetworkObj.enumAsk()

StartNetwork=load()
StartNetwork.Bootup()


