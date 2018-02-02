from enum import Enum
from graphviz import Graph, Digraph
from copy import deepcopy

class OPType(Enum):
    Star = 1
    Plus = 2
    Concat = 3
    Symbol = 4
    Union = 5
    Questionmark = 6


def tokenize(txt):
    out = []
    colonActive = False
    numParen = 0
    specialChar = ""

    for c in txt:
        if colonActive:
            specialChar += c
            if c == ':':
                out.append(specialChar)
                colonActive = False
                specialChar = ""

        elif numParen > 0:
            specialChar += c
            if c == ")":
                numParen -= 1
                if numParen == 0:
                    out.append(specialChar)
                    specialChar = ""
            elif c == "(":
                numParen += 1

        else:
            if c == ":":
                colonActive = True
                specialChar = ":"
            elif c == "(":
                numParen += 1
                specialChar = "("
            else:
                out.append(c)

    if colonActive:
        raise ValueError(
            "Terminating colon missing when parsing special character (like :space:, but the last colon is missing -> :space )"
        )
    if numParen > 0:
        raise ValueError(
            "Terminating parentheses missing. In total: " + str(numParen))

    return out


def build_concatExprTree(list_):
    if len(list_) == 1:
        return list_[0]
    lhs = list_[0]
    rhs = build_concatExprTree(list_[1:])
    return Expression(OPType.Concat, lhs, rhs)


def make_expr(expr):
    operandMap = {"*" : OPType.Star, "+" : OPType.Plus, "?" : OPType.Questionmark}
    def inner(exprList):
        # precedence: *,+: unary; @:1; |:0
        if not exprList:
            raise ValueError("Empty Expression")
        treeList = []
        for i in range(len(exprList)):
            subExpr = exprList[i]
            if subExpr.startswith("("):
                convToList = tokenize(subExpr[1:len(subExpr) - 1])
                treeList.append(inner(convToList))
            elif subExpr.startswith("*") or subExpr.startswith("+") or subExpr.startswith("?"):
                if (len(treeList) == 0):
                    raise ValueError(
                        "Expected a left hand operand when parsing */+, but none was given"
                    )
                lhs = treeList.pop()
                parentExpr = Expression(
                    operandMap[subExpr[0]], lhs)
                treeList.append(parentExpr)
            elif subExpr.startswith("|"):
                if len(treeList) == 0:
                    raise ValueError(
                        "Expected left hand operand when parsing a '|', but none was given"
                    )
                lhs = build_concatExprTree(
                    treeList)  # the tree list only consists of concat ops.
                rhsUnparsed = exprList[i + 1:]
                if len(rhsUnparsed) == 0:
                    raise ValueError(
                        "Expected right hand operand when parsing a '|', but none was given"
                    )
                rhs = inner(rhsUnparsed)
                return Expression(OPType.Union, lhs, rhs)
            else:  # It is a symbol
                treeList.append(Expression(OPType.Symbol, None, None, subExpr))
        return build_concatExprTree(treeList)

    return inner(tokenize(expr))


class Expression:
    def __init__(self, opType, lhs=None, rhs=None, symbol=None):
        #split = re.split("\*|\+|\\([^)]*\\)|:num:|:space:|:alpha:|\W*",raw)

        self.lhs = lhs
        self.rhs = rhs
        self.opType = opType
        self.symbol = symbol

    def isConcat(self):
        return self.opType == OPType.Concat

    def isUnion(self):
        return self.opType == OPType.Union

    def isStar(self):
        return self.opType == OPType.Star

    def isSymbol(self):
        return self.opType == OPType.Symbol

    def isPlus(self):
        return self.opType == OPType.Plus

    def getSymbol(self):
        return self.symbol

    def isQuestionmark(self):
        return self.opType == OPType.Questionmark


class Transition:
    def __init__(self, from_, to, transVar):
        self.transVar = transVar
        self.from_ = from_
        self.to = to

# Better encapsulation?
class State:
    def __init__(self, isInitState = False, isFinalState = False):
        self.__transIn = []  # transitions to other states
        self.__transOut = []

        self.__final = isFinalState
        self.__init =  isInitState

    def isFinal(self):
        return self.__final

    def isInit(self):
        return self.__init
    
    def connectTo(self, to, transVar=":e:", allowMultipleTransitionToInitState=True, allowMultipleTransitionsFromOutputState=True):
        trans = Transition(self, to, transVar)
        self.disconnect(to, transVar)  # First of all, disconnect if connected
        if allowMultipleTransitionsFromOutputState:
            self.__final = False
        self.__transOut.append(trans)

        if allowMultipleTransitionToInitState:
            to.__init = False
        to.__transIn.append(trans)

    def iterateOutNeighbours(self):
        for i in self.__transOut:
            yield (i.to, i)

    def iterateInNeighbours(self):
        for i in self.__transIn:
            yield (i.from_, i)


    def disconnect(self, to, withTransVar):
        for index in range(len(self.__transOut)):
            trans = self.__transOut[index]
            if trans.to == to and trans.transVar == withTransVar:
                trans.to.__transIn.remove(trans)
                del self.__transOut[index]
                return      

class NameGen:
    def __init__(self, keepSetAsName):
        self.counter = -1
        self.keep = keepSetAsName
    def gen_state_name(self,frozenSetToBeNamed):
        #assert type(frozenSetToBeNamed) is frozenset()
        if self.keep:
            return str(frozenSetToBeNamed).replace("frozenset","").replace("(","").replace(")","").replace("'","")
        else:
            self.counter += 1
            return str(self.counter)


class TransitionTable:
    def __init__(self):
        self.table = [[]]
        self.stateNames = {}
        self.transNames = {}
        self.finalStates = set()
        self.initStates  = set()

    def assert_exists_transition(self,transVar):
        if not transVar in self.transNames:
            for item in self.table:
                item.append(set())
            self.transNames[transVar] = len(self.table[0])-1
            return False # didn't exist
        return True
 
 
    def assert_exists(self,state, isFinal,isInit):
        if not state in self.stateNames:
            to_insert = []
            for _ in self.table[0]:
                to_insert.append(set())
            self.table.append(to_insert)
            self.stateNames[state] = len(self.table)-1
            if isInit:
                self.initStates.add(state)
            if isFinal:
                self.finalStates.add(state)
            return False
        return True

    def make_transition(self,from_,to,transVar, isFromFinal=False, isFromInit=False, isToFinal = False, isToInit=False):
        # Check if the transition variable is new
        existed = self.assert_exists_transition(transVar)
        # Check if from_ and to exists                    
        existed = self.assert_exists(from_,isFromFinal,isFromInit) and existed
        existed = self.assert_exists(to,isToFinal,isToInit) and existed
        self.table[self.stateNames[from_]][self.transNames[transVar]].add(to)
        return existed
 
    
    def iterateStates(self):
        for state in self.stateNames.keys():
            yield (True if state in self.initStates else False,True if state in self.finalStates else False,state)

    def iterateTransitions(self):
        for from_,i in self.stateNames.items():
            for transVar,j in self.transNames.items():
                toStates = self.table[i][j]
                for to in toStates:
                    yield (from_, to,transVar)

    def get(self,state,trans):
        return self.table[self.stateNames[state]][self.transNames[trans]]
   
    # TODO: what about states that are 
    def set(self,state,trans,var):
        assert not(state is None)
        assert type(var) is set
        self.table[self.stateNames[state]][self.transNames[trans]] = var

    def to_Estar(self):
        generated = deepcopy(self)
        generated.assert_exists_transition(":e:")
        def from_state(startState):
            Estar = {startState} # E^0
            activeStates = [startState]
            while activeStates:
                state = activeStates.pop()
                for to in generated.get(state,":e:"):
                    if not to in Estar:
                        Estar.add(to)
                        activeStates.append(to)
            return Estar

        deferred = []
        for stateName in generated.stateNames.keys():
            Estar = from_state(stateName)
            deferred.append( (lambda x,y: generated.set(x,":e:",y),stateName,Estar) )
        
        for update,x,y in deferred:
            update(x,y)

        return generated

    # TODO: Improve code, it's just ugly. Variables are badly named.
    def remove_epsilon_trans(self, keepSetAsName = False):
        self = self.to_Estar()
        gen = NameGen(keepSetAsName)
        nfa = TransitionTable()
        activeSimulatedStates = set()
        generatedStates = {}
        for initState in self.initStates: 
            frozenInitStateSet = frozenset(self.get(initState,":e:"))
            activeSimulatedStates.add(frozenInitStateSet)
            generatedStates[frozenInitStateSet] = gen.gen_state_name(frozenInitStateSet)
            
        #Simulate 
        while activeSimulatedStates:
            stateFromSet = activeSimulatedStates.pop()
            stateFromSetName = generatedStates[stateFromSet]
            isFromFinal = any(x in self.finalStates for x in stateFromSet)
            isFromInit = any(x in self.initStates for x in stateFromSet)
            # Try to transit deterministically and then take all :e: transitions
            for state in stateFromSet:
                for trans in self.transNames:
                    if trans == ":e:": continue
                    nextStateSet = self.get(state,trans)
                    # now for each state try to take epsilon transitions:
                    for stateEps in nextStateSet:
                        stateToSet = frozenset(self.get(stateEps,":e:"))
                        isToFinal = any(x in self.finalStates for x in stateToSet)
                        isToInit = any(x in self.initStates for x in stateToSet)
                        if not stateToSet in generatedStates: 
                            stateToSetName = gen.gen_state_name(stateToSet)
                            nfa.make_transition(stateFromSetName,stateToSetName,trans,isFromFinal,isFromInit,isToFinal,isToInit)
                            activeSimulatedStates.add(stateToSet)
                            generatedStates[stateToSet] = stateToSetName
                        else:
                            stateToSetName = generatedStates[stateToSet]
                            nfa.make_transition(stateFromSetName,stateToSetName,trans,isFromFinal,isFromInit,isToFinal,isToInit)
                            

        return nfa

    #Similar to epsilon removal, but now i don't have to take epsilon transitions anymore.
    #TODO: Maybe merge both algorithms? Code redundancy is an issue here.
    #TODO: Possible even slower because I have to go through all the transition variables!
    def to_dfa(self, keepStateNames = False):
        gen = NameGen(keepStateNames)
        frozenInitStates = frozenset(self.initStates)
        activeSimulatedStates = {frozenInitStates}
        generatedStates = {frozenInitStates : gen.gen_state_name(frozenInitStates)}
        self = self.remove_epsilon_trans(False) 
        dfa = TransitionTable()

        while activeSimulatedStates:
            stateFromSet = activeSimulatedStates.pop()
            stateFromSetName = generatedStates[stateFromSet]
            isFromFinal = any(x in self.finalStates for x in stateFromSet)
            isFromInit = any(x in self.initStates for x in stateFromSet)
            for trans in self.transNames:
                collectedSimulatedStates = set()
                isToFinal = False
                isToInit = False
                for state in stateFromSet:
                    stateToSet = self.get(state,trans)
                    if stateToSet: 
                        collectedSimulatedStates = collectedSimulatedStates.union(stateToSet)
                        isToFinal = any(x in self.finalStates for x in stateToSet) or isToFinal
                        isToInit = any(x in self.initStates for x in stateToSet) or isToInit
                if not collectedSimulatedStates: continue
                frozenCollectedStates = frozenset(collectedSimulatedStates)
                if not frozenCollectedStates in generatedStates: 
                    newStateSetName = gen.gen_state_name(frozenCollectedStates)
                    dfa.make_transition(stateFromSetName,newStateSetName,trans,isFromFinal,isFromInit,isToFinal,isToInit)
                    activeSimulatedStates.add(frozenCollectedStates)
                    generatedStates[frozenCollectedStates] = newStateSetName
                else:
                    newStateSetName = generatedStates[frozenCollectedStates]
                    dfa.make_transition(stateFromSetName,newStateSetName,trans,isFromFinal,isFromInit,isToFinal,isToInit)

        
        return dfa     

class NFA:
    def __init__(self):
        self.make_init()
        self.make_final()
        self.__transtable_dirty = True
        self.__transTable = TransitionTable() 

    def make_init(self):
        self.initState = State(isInitState = True)
        return self.initState

    def make_final(self):
        self.finalState = State(isFinalState = True)
        return self.finalState
#### Setter & Getter
    @property
    def initState(self):
        return self.__initState

    @initState.setter
    def initState(self,value):
        self.__transtable_dirty = True
        self.__initState = value

    @property
    def finalState(self):
        return self.__finalState

    @finalState.setter
    def finalState(self,value):
        self.__transtable_dirty = True
        self.__finalState = value

    @property
    def transitionTable(self):
        def iterateCallback(from_,to,nameFrom,nameTo,transVar):
            self.__transTable.make_transition(nameFrom,nameTo,transVar,from_.isFinal(),from_.isInit(), to.isFinal(), to.isInit())
        
        if self.__transtable_dirty:
            self.__transTable = TransitionTable()
            self.iterateGraph(iterateCallback)
            self.__transtable_dirty = False
        return self.__transTable
        
    
#### End

    def copy(self, other):
        self.finalState = other.finalState
        self.initState = other.initState

    def concatV2(self, other):
        for (stateIn, trans) in list(self.finalState.iterateInNeighbours()):  #iterate over copy because disconnect changes the iterator!
            stateIn.disconnect(self.finalState, trans.transVar)
            stateIn.connectTo(other.initState, trans.transVar)
        
        self.finalState = other.finalState
        #draw_fa(self,"after concat")

    def concatV1(self, other):
        self.finalState.connectTo(other.initState)
       

    def union(self, other):
        out = NFA()
        out.initState.connectTo(self.initState)
        out.initState.connectTo(other.initState)
        self.finalState.connectTo(out.finalState)
        other.finalState.connectTo(out.finalState)
        self.copy(out)

    def starV1(self):
        #draw_fa(self, "start star")
        out = NFA()
        out.initState.connectTo(out.finalState)
        #draw_fa(out, "outinit connect to outfinal")
        out.initState.connectTo(self.initState)
        #draw_fa(out, "outinit connect to selfinit")
        self.finalState.connectTo(self.initState)
        #draw_fa(self, "selffinal to selfinit")
        self.finalState.connectTo(out.finalState)
        #draw_fa(out, "selffinal to outfinal")
        self.copy(out)
        #draw_fa(out, "after copy");

    def starV2(self):
        out = NFA()
        out.initState.connectTo(out.finalState)
        out.initState.connectTo(self.initState)
        self.finalState.connectTo(out.initState, allowMultipleTransitionToInitState=False) # Make sure we can keep the init state even though now a transition goes back to it (Thompson's construction originally doesn't need this, so that's why I added this option)
        self.copy(out)

    def plus(self):
        #draw_fa(self,"Start op")
        self.starV1()
        #draw_fa(self,"Starred")
        self.initState.disconnect(self.finalState,":e:")
        #draw_fa(self,"Disconnect thingy")

    def symbol(self, a):
        self.initState.connectTo(self.finalState, a)
    
    def questionmark(self):
        out = NFA()
        out.initState.connectTo(out.finalState)
        out.initState.connectTo(self.initState)
        self.finalState.connectTo(out.finalState)
        self.copy(out)
         
        
    # TODO: Improve in order to replace ugly dfs code everywhere
    def iterateGraph(self, callback):
        counter = 0
        visited = {}

        #Inner sets the correct name and performs a dfs on to.
        def inner(state):
            nonlocal counter
            visited[state] = counter
            strCounter = str(counter)
            counter += 1
            for to,trans in state.iterateOutNeighbours():
                if not to in visited:
                    inner(to)
                callback( state,to,strCounter,str(visited[to]),trans.transVar )

        return inner(self.initState)

                               

def make_nfa(expr):
    #print(expr.opType)
    if expr.isConcat():  # st
        dfaLhs = make_nfa(expr.lhs)
        dfaRhs = make_nfa(expr.rhs)
        dfaLhs.concatV2(dfaRhs)
        return dfaLhs

    elif expr.isUnion():
        dfaLhs = make_nfa(expr.lhs)
        dfaRhs = make_nfa(expr.rhs)
        dfaLhs.union(dfaRhs)
        return dfaLhs

    elif expr.isStar():
        dfaLhs = make_nfa(expr.lhs)
        dfaLhs.starV1()
        return dfaLhs

    elif expr.isPlus():
        dfaLhs = make_nfa(expr.lhs)
        dfaLhs.plus()
        return dfaLhs

    elif expr.isSymbol():
        dfaLhs = NFA()
        dfaLhs.symbol(expr.getSymbol())
        return dfaLhs

    elif expr.isQuestionmark():
        dfaLhs = make_nfa(expr.lhs)
        dfaLhs.questionmark()
        return dfaLhs


def draw_expr(expr, title):
    graph = Graph(title, filename=title)
    graph.attr(rankdir="TD", size="50")
    typeMapper = {
        OPType.Star: "*",
        OPType.Plus: "+",
        OPType.Concat: "@",
        OPType.Union: "|",
        OPType.Symbol: "S",
        OPType.Questionmark : "?"
    }
    counter = 0

    def inner(expr):
        nonlocal counter
        label_ = ""
        color_ = "red"
        if expr.isSymbol():
            label_ = expr.getSymbol()
            color_ = "blue"
        else:
            label_ = typeMapper[expr.opType]
        graph.node(str(counter), shape="circle", label=label_, color=color_)
        expr.name = str(counter)  # Monkey patching !!
        counter += 1
        if expr.lhs != None:
            inner(expr.lhs)
            graph.edge(expr.name, expr.lhs.name)
        if expr.rhs != None:
            inner(expr.rhs)
            graph.edge(expr.name, expr.rhs.name)

    inner(expr)
    graph.view()

#TODO: Draw based on transition table, don't do a dfs!
def draw_fa(ttable, title):
    graph = Digraph(title, filename=title)
    graph.attr(rankdir='LR', size="50")
   
    for isInit,isFinal,state in ttable.iterateStates():
        shape_ = "circle"
        color_ = "black"
        if isFinal:
            shape_ = "doublecircle"
        if isInit:
            color_ = "blue"
        graph.node(state,shape=shape_,color=color_)

    for from_,to,transVar in ttable.iterateTransitions():
        graph.edge(from_,to,transVar)

    graph.view()

##### C++ generation

def parse_source(filename):
    pass





a = make_expr("ret|re(te)*")
#a = make_expr("a|a|b*")
b = make_nfa(a)
draw_expr(a, "Expression")
t = b.transitionTable
draw_fa(t, "eNFA")
draw_fa(t.to_Estar(),"Estar") 
draw_fa(t.remove_epsilon_trans(False),"NFA")
draw_fa(t.to_dfa(False),"DFA!!")
print("END")











