import re
import operator
import copy
import sys

allowed_operators = {
    ">": operator.gt,
    "<": operator.lt,
    "=": operator.eq,
    "!": operator.ne}

def main():
    global counter
    counter = 0
    variableList = {}
    with open(sys.argv[1], errors='ignore') as input_file:
        for i, line in enumerate(input_file):
            line = re.sub(r'\n', '', line)
            line = re.sub(r'[ \t]+$', '', line)
            variable = Variable()
            variable.label = line[0]
            tempDom = []
            for l in line[3:].split(' '):
                tempDom.append(int(l))
            variable.domain = tempDom
            variable.assignment = None
            variableList[variable.label] = variable

    constraints = []
    with open(sys.argv[2], errors='ignore') as input_file:
        for i, line in enumerate(input_file):
            line = re.sub(r'\n', '', line)
            line = re.sub(r'[ \t]+$', '', line)
            constraints.append((line[0], line[2], line[4]))

    # changer ceci en une fonction basée sur arg3 plus tard
    
    if sys.argv[3] == "none":
        #print(type(sys.argv[3]))
        forward_checking = False
    else:
        forward_checking = True

    vas = recursive_backtracking({}, variableList, constraints, forward_checking)
    if vas is not False:
        c = 0
        counter += 1
        print(counter, ". ", end="", sep="")
        for v in vas.keys():
            if c is len(vas.keys()) - 1:
                print(v, "=", vas[v], " solution", sep="")
            else:
                print(v, "=", vas[v], ", ", end="", sep="")
            c += 1


class Variable():
    label = None
    domain = None
    assignment = None

counter = 0

def recursive_backtracking(assigned, variableList, constraints, forward_checking):
    global counter
    if all(variable.assignment != None for variable in variableList.values()):
        return assigned

    var = select_unassigned_variable(variableList, constraints)

    orderedDomain = sorted_domain(variableList, constraints, var)
    
    for vals in orderedDomain:
        for val in vals:
            # si la valeur est cohérente avec l'affectation selon les contraintes
            val = int(val)
            flag = True
            for cons in constraints:
                if cons[0] is variableList[var].label:
                    if variableList[cons[2]].assignment is None:
                        continue
                    else:
                        flag = allowed_operators[cons[1]](val, int(variableList[cons[2]].assignment))
                        
                elif cons[2] is variableList[var].label:
                    if variableList[cons[0]].assignment is None:
                        continue
                    else:
                        flag = allowed_operators[cons[1]](int(variableList[cons[0]].assignment), val)
                        
                if flag is False:
                    c = 0
                    counter += 1
                    print(counter, ". ", end="", sep="")
                    for v in assigned.keys():
                        if c is len(assigned.keys()) - 1:
                            print(v, "=", assigned[v], ", ", end="", sep="")
                            print(variableList[var].label, "=", val, " failure", sep="")
                        else:
                            print(v, "=", assigned[v], ", ", end="", sep="")
                        c += 1
                    if counter >= 30:
                        SystemExit
                    break

            if flag is True:
                variableList[var].assignment = val
                assigned[var] = val
                resultVariableList = None
                #vérifier ici
                if forward_checking is True:
                    #restreindre les domaines en fonction de l'attribution
                    resultVariableList = forward_checking_function(copy.deepcopy(variableList), constraints, var)
                    #bit pour s'assurer qu'aucun domaine n'est vide, si l'un est alors renvoyé faux
                    for variable in resultVariableList.values():
                        if len(variable.domain) is 0:
                            c = 0
                            counter += 1
                            print(counter, ". ", end="", sep="")
                            for v in assigned.keys():
                                if c is len(assigned.keys()) - 1:
                                    #print(v, "=", assigned[v], ", ", end="", sep="")
                                    print(variableList[var].label, "=", val, " failure", sep="")
                                else:
                                    print(v, "=", assigned[v], ", ", end="", sep="")
                                c += 1
                            if counter >= 30:
                                SystemExit
                            continue
                else:
                    resultVariableList = variableList

                result = recursive_backtracking(assigned, resultVariableList, constraints, forward_checking)
                if result is not False:
                    return result
                variableList[var].assignment = None
                assigned.pop(var)
    
    return False


def forward_checking_function(variableList, constraints, var):
    assignedValue = variableList[var].assignment
    # supprimer des valeurs d'autres domaines variables qui ne respectent pas les contraintes
    for cons in constraints:
        if cons[0] is variableList[var].label:
            # si une autre variable dans la contrainte n'est pas affectée, restreigner le domaine
            if variableList[cons[2]].assignment is None:
                removalList = []
                for value in variableList[cons[2]].domain:
                    if allowed_operators[cons[1]](assignedValue, value) is False:
                        removalList.append(value)
                
                for r in removalList:
                    variableList[cons[2]].domain.remove(r)
   
        elif cons[2] is variableList[var].label:
            # si une autre variable dans la contrainte n'est pas affectée, restreigner le domaine
            if variableList[cons[0]].assignment is None:
                removalList = []
                for value in variableList[cons[0]].domain:
                    if allowed_operators[cons[1]](value, assignedValue) is False:
                        removalList.append(value)
                for r in removalList:
                    variableList[cons[0]].domain.remove(r)
                        
    return variableList


def select_unassigned_variable(variables, constraints):
    var = None
    varList = []
    for v in variables.keys():
        # si laa variable n'a pas d'affectation
        if variables[v].assignment == None:
            # si aucune variable en cours de vérification, prendre simplement la première
            if var == None:
                var = v
                varList.append(v)
            # véfier le plus contraint
            elif len(variables[var].domain) > len(variables[v].domain):
                var = v
                varList = [v]
            # sinon si l'égalité est contrainte, alors chercher d'égalité la plus contraignante
            elif len(variables[var].domain) == len(variables[v].domain):
                varcount = 0
                variablecount = 0
                # comparer les interactions de contrainte de meilleure valeur actuelles si elles se trouvent sur le côté gauche de la contrainte
                varcount += sum(
                    1 for i in constraints if i[0] == variables[var].label and variables[i[2]].assignment == None)
                # comparer les interactions de contrainte de meilleure valeur actuelles si elles se trouvent sur le côté droit de la contrainte
                varcount += sum(
                    1 for i in constraints if variables[i[0]].assignment == None and i[2] == variables[var].label)
                # comparer les interactions de contrainte d'itération en cours si elles se trouvent sur le côté gauche de la contrainte
                variablecount += sum(
                    1 for i in constraints if i[0] == variables[v].label and variables[i[2]].assignment == None)
                # comparer les interactions de contrainte d'itération en cours si elles se trouvent sur le côté droit de la contrainte
                variablecount += sum(
                    1 for i in constraints if variables[i[0]].assignment == None and i[2] == variables[v].label)
                # si la nouvelle variable a un nombre d'interactions de contraintes plus élevé, alors rendre la meilleure actuelle
                if varcount < variablecount:
                    var = v
                    varList = [v]
                elif varcount == variablecount:
                    varList.append(v)
    
    return var


def sorted_domain(variableList, constraints, var):
    # créer un tableau qui contient les valeurs contraignantes pour chaque variable
    constrainingValues = {}
    for val in variableList[var].domain:
        val = int(val)
        tempValue = 0
        for cons in constraints:
            
            if cons[0] is variableList[var].label and variableList[cons[2]].assignment is None:
                for compValue in variableList[cons[2]].domain:
                    if not allowed_operators[cons[1]](val, int(compValue)):
                        tempValue += 1
            elif variableList[cons[0]].assignment is None and cons[2] == variableList[var].label:
                for compValue in variableList[cons[0]].domain:
                    if not allowed_operators[cons[1]](int(compValue), val):
                        tempValue += 1
        
        if tempValue in constrainingValues:
            constrainingValues[tempValue].append(int(val))
        else:
            constrainingValues[tempValue] = [int(val)]

    orderedDomain = []
    for s in sorted(constrainingValues.keys()):
        orderedDomain.append(constrainingValues[s])

    return orderedDomain


if __name__ == "__main__":
    main()

