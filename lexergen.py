from enum import Enum
from graphviz import Graph, Digraph
from copy import deepcopy
from itertools import chain
from functools import reduce

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
    handleAsSymbol = False

    for c in txt:
        if handleAsSymbol or c == '°':
            out.append(c)
            handleAsSymbol =  not handleAsSymbol
            continue           

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
    specialCharMap = {":num:" : "0|1|2|3|4|5|6|7|8|9", ":capalpha:" : "A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z", ":camalpha:" : "a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z", ":alpha:" : ":capalpha: | :camalpha:"  }
    def inner(exprList):
        # precedence: *,+: unary; @:1; |:0
        if not exprList:
            raise ValueError("Empty Expression")
        treeList = []
        handleAsSymbol = False
        for i in range(len(exprList)):
            subExpr = exprList[i]
            if handleAsSymbol:
                treeList.append(Expression(OPType.Symbol,symbol=subExpr))
                handleAsSymbol = False
                continue

            if subExpr.startswith(":"):
                convToList = tokenize(specialCharMap[subExpr])
                treeList.append(inner(convToList))

            elif subExpr.startswith("("):
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
            elif subExpr.startswith("°"):
                handleAsSymbol = True

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
    def __init__(self, isInitState = False, isAcceptState = False, label=""):
        self.__transIn = []  # transitions to other states
        self.__transOut = []

        self.__accept = isAcceptState
        self.__init =  isInitState
        self.label = label

    def isAccept(self):
        return self.__accept

    def isInit(self):
        return self.__init
    
    def connectTo(self, to, transVar=":e:", allowMultipleTransitionToInitState=True, allowMultipleTransitionsFromOutputState=True):
        trans = Transition(self, to, transVar)
        self.disconnect(to, transVar)  # First of all, disconnect if connected
        if allowMultipleTransitionsFromOutputState:
            self.__accept = False
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
        self.acceptStates = set()
        self.initStates  = set()
        self.labelMap = {}

    def assert_exists_transition(self,transVar):
        if not transVar in self.transNames:
            for item in self.table:
                item.append(set())
            self.transNames[transVar] = len(self.table[0])-1
            return False # didn't exist
        return True
 
 
    def assert_exists(self,state, isAccept,isInit):
        if not state in self.stateNames:
            to_insert = []
            for _ in self.table[0]:
                to_insert.append(set())
            self.table.append(to_insert)
            self.stateNames[state] = len(self.table)-1
            if isInit:
                self.initStates.add(state)
            if isAccept:
                self.acceptStates.add(state)
            return False
        return True

    def make_transition(self,from_,to,transVar, isFromAccept=False, isFromInit=False, isToaccept = False, isToInit=False,fromLabel = "", toLabel=""):
        # Check if the transition variable is new
        existed = self.assert_exists_transition(transVar)
        # Check if from_ and to exists                    
        existed = self.assert_exists(from_,isFromAccept,isFromInit) and existed
        existed = self.assert_exists(to,isToaccept,isToInit) and existed
        self.table[self.stateNames[from_]][self.transNames[transVar]].add(to)
        self.labelMap[from_] = fromLabel
        self.labelMap[to] = toLabel 
        return existed
    
    def relabel(self,state,newLabel):
        self.labelMap[state] = newLabel

    def iterateStates(self):
        for state in self.stateNames.keys():
            label = self.labelMap[state]
            yield (True if state in self.initStates else False,True if state in self.acceptStates else False,state,label)

    def iterateTransitions(self):
        for from_,i in self.stateNames.items():
            for transVar,j in self.transNames.items():
                toStates = self.table[i][j]
                for to in toStates:
                    yield (from_, to,transVar)

    def iterateTransitionsFor(self, state):
        for transVar,i in self.transNames.items():
            for to in self.get(state,transVar):
                yield (to,transVar)

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
            isFromAccept = any(x in self.acceptStates for x in stateFromSet)
            isFromInit = any(x in self.initStates for x in stateFromSet)
            labelFromSet = self.gen_label(stateFromSet)
            # Try to transit deterministically and then take all :e: transitions
            for state in stateFromSet:
                for trans in self.transNames:
                    if trans == ":e:": continue
                    nextStateSet = self.get(state,trans)
                    # now for each state try to take epsilon transitions:
                    for stateEps in nextStateSet:
                        stateToSet = frozenset(self.get(stateEps,":e:"))
                        isToAccept = any(x in self.acceptStates for x in stateToSet)
                        isToInit = any(x in self.initStates for x in stateToSet)
                        labelToSet = self.gen_label(stateToSet)
                        if not stateToSet in generatedStates: 
                            stateToSetName = gen.gen_state_name(stateToSet)
                            nfa.make_transition(stateFromSetName,stateToSetName,trans,isFromAccept,isFromInit,isToAccept,isToInit,labelFromSet,labelToSet)
                            activeSimulatedStates.add(stateToSet)
                            generatedStates[stateToSet] = stateToSetName
                        else:
                            stateToSetName = generatedStates[stateToSet]
                            nfa.make_transition(stateFromSetName,stateToSetName,trans,isFromAccept,isFromInit,isToAccept,isToInit,labelFromSet,labelToSet)
                            

        return nfa

    def gen_label(self,states):
        label = ""
        for state in states:
            label+=self.labelMap[state]+" "
        return label.strip() 

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
            isFromAccept = any(x in self.acceptStates for x in stateFromSet)
            isFromInit = any(x in self.initStates for x in stateFromSet)
            fromSetLabel = self.gen_label(stateFromSet)
            for trans in self.transNames:
                collectedSimulatedStates = set()
                isToAccept = False
                isToInit = False
                toSetLabel = ""
                for state in stateFromSet:
                    stateToSet = self.get(state,trans)
                    if stateToSet: 
                        collectedSimulatedStates = collectedSimulatedStates.union(stateToSet)
                        isToAccept = any(x in self.acceptStates for x in stateToSet) or isToAccept
                        isToInit = any(x in self.initStates for x in stateToSet) or isToInit
                        toSetLabel = self.gen_label(stateToSet)
                if not collectedSimulatedStates: continue
                frozenCollectedStates = frozenset(collectedSimulatedStates)
                if not frozenCollectedStates in generatedStates: 
                    newStateSetName = gen.gen_state_name(frozenCollectedStates)
                    dfa.make_transition(stateFromSetName,newStateSetName,trans,isFromAccept,isFromInit,isToAccept,isToInit,fromSetLabel,toSetLabel)
                    activeSimulatedStates.add(frozenCollectedStates)
                    generatedStates[frozenCollectedStates] = newStateSetName
                else:
                    newStateSetName = generatedStates[frozenCollectedStates]
                    dfa.make_transition(stateFromSetName,newStateSetName,trans,isFromAccept,isFromInit,isToAccept,isToInit,fromSetLabel,toSetLabel)

        
        return dfa     


class NFA:
    def __init__(self):
        self.make_init()
        self.make_accept()
        self.__transtable_dirty = True
        self.__transTable = TransitionTable() 

    def make_init(self):
        self.initState = State(isInitState = True)
        return self.initState

    def make_accept(self):
        self.acceptState = State(isAcceptState = True)
        return self.acceptState

# TODO: Probably performance considerations (settings transtable dirty and not dirty by only accessing a state.)
#### Setter & Getter
    @property
    def initState(self):
        self.__transtable_dirty = True
        return self.__initState

    @initState.setter
    def initState(self,value):
        self.__transtable_dirty = True
        self.__initState = value

    @property
    def acceptState(self):
        self.__transtable_dirty = True
        return self.__acceptState

    @acceptState.setter
    def acceptState(self,value):
        self.__transtable_dirty = True
        self.__acceptState = value

    @property
    def transitionTable(self):
        def iterateCallback(from_,to,nameFrom,nameTo,transVar):
            self.__transTable.make_transition(nameFrom, nameTo,transVar,from_.isAccept(),from_.isInit(), to.isAccept(), to.isInit(),from_.label,to.label)
        
        if self.__transtable_dirty:
            self.__transTable = TransitionTable()
            self.iterateGraph(iterateCallback)
            self.__transtable_dirty = False
        return self.__transTable
         
#### End

    def copy(self, other):
        self.acceptState = other.acceptState
        self.initState = other.initState

    def concatV2(self, other):
        for (stateIn, trans) in list(self.acceptState.iterateInNeighbours()):  #iterate over copy because disconnect changes the iterator!
            stateIn.disconnect(self.acceptState, trans.transVar)
            stateIn.connectTo(other.initState, trans.transVar)
        
        self.acceptState = other.acceptState
        #draw_fa(self,"after concat")

    def concatV1(self, other):
        self.acceptState.connectTo(other.initState)
       

    def union(self, other):
        out = NFA()
        out.initState.connectTo(self.initState)
        out.initState.connectTo(other.initState)
        self.acceptState.connectTo(out.acceptState)
        other.acceptState.connectTo(out.acceptState)
        self.copy(out)

    def starV1(self):
        #draw_fa(self, "start star")
        out = NFA()
        out.initState.connectTo(out.acceptState)
        #draw_fa(out, "outinit connect to outaccept")
        out.initState.connectTo(self.initState)
        #draw_fa(out, "outinit connect to selfinit")
        self.acceptState.connectTo(self.initState)
        #draw_fa(self, "selfaccept to selfinit")
        self.acceptState.connectTo(out.acceptState)
        #draw_fa(out, "selfaccept to outaccept")
        self.copy(out)
        #draw_fa(out, "after copy");

    def starV2(self):
        out = NFA()
        out.initState.connectTo(out.acceptState)
        out.initState.connectTo(self.initState)
        self.acceptState.connectTo(out.initState, allowMultipleTransitionToInitState=False) # Make sure we can keep the init state even though now a transition goes back to it (Thompson's construction originally doesn't need this, so that's why I added this option)
        self.copy(out)

    def plus(self):
        #draw_fa(self,"Start op")
        self.starV1()
        #draw_fa(self,"Starred")
        self.initState.disconnect(self.acceptState,":e:")
        #draw_fa(self,"Disconnect thingy")

    def symbol(self, a):
        self.initState.connectTo(self.acceptState, a)
    
    def questionmark(self):
        out = NFA()
        out.initState.connectTo(out.acceptState)
        out.initState.connectTo(self.initState)
        self.acceptState.connectTo(out.acceptState)
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


def draw_expr(expr, title="Standard Expression"):
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
def draw_fa(ttable, title="Standard FA"):
    graph = Digraph(title, filename=title)
    graph.attr(rankdir='LR', size="50")
   
    for isInit,isAccept,state,label in ttable.iterateStates():
        shape_ = "circle"
        color_ = "black"
        if isAccept:
            shape_ = "doublecircle"
        if isInit:
            color_ = "blue"
        if label:
            graph.node(state,shape=shape_,color=color_, label=label)
        else:
            graph.node(state,shape=shape_,color=color_)


    for from_,to,transVar in ttable.iterateTransitions():
        graph.edge(from_,to,transVar)

    graph.view()

##### C++ generation

def extract(text,kw):
    pos = text.find(kw)
    if pos < 0:
        return []
    
    extractBlock = text[pos:]
    start = extractBlock.find("<start>")+8 # 8 == number of chars of <start> + newline
    end = extractBlock.find("</end>")
    return filter(bool,extractBlock[start:end].split("\n"))

def parse_source(filename):
    spec = open(filename).read()
    ids = extract(spec,"id")
    ids = map(lambda x: (x,x),ids)
    map_backs = extract(spec,"map_back")
    capture_lexemes = extract(spec,"capture_lexeme")
    toTuple = lambda transList: map(lambda x: (x[0].replace(" ",""), x[1].replace(" ","")),map(lambda x: x.split("-",maxsplit=1), transList))
    map_backs = toTuple(map_backs)
    capture_lexemes = toTuple(capture_lexemes)
    return chain(ids,map_backs,capture_lexemes)

class CPPLexer:
    def __init__(self, dfaTable):
       
        includes = """
        #pragma once
        #include <string>
        #include <cassert>\n\n
        """

        tokenInformationStruct = """
        struct TokenInfo
        {
            int Type;
            std::string Lexeme;
            std::string Filename;
            size_t Line;
            size_t Position;
        };"""

        tokenTypeEnum = """
        namespace TokenType
        {
            enum
            {
                <definition_token_type_enum>
            };
        };"""

        lexerClass = """
        template<typename TSourceCodeProvider>
        class Lexer
        {
        public:
            Lexer(TSourceCodeProvider&& provider_) : provider(std::move(provider_)) 
            {
                start_char = provider.Next();
            }

            TokenInfo Eat()
            {
                TokenInfo tmp = current_token_info;
                assign_next_token();
                return tmp;
            }

            TokenInfo Peek()
            {
                return current_token_info;
            }

        private:
            TSourceCodeProvider provider;
            TokenInfo current_token_info;
            char start_char;
            void assign_next_token()
            {
                char c;
                std::string matched_word;
                std::string filename = provider.current_filename();
                size_t startedLine = provider.current_line();
                size_t startedPosition = provider.current_cursor_pos();
                <definition_assign_next_token>
            }
        };"""

        self.dfaTable = dfaTable

        method_def, tokenTypesCode = self.genCode()
        lexerClass = lexerClass.replace("<definition_assign_next_token>", method_def)
        tokenTypeEnum = tokenTypeEnum.replace("<definition_token_type_enum>", tokenTypesCode)

        self.generatedCode = includes + tokenTypeEnum + tokenInformationStruct + lexerClass

    def save(self, filename):
        f = open(filename,"w")
        f.write(self.generatedCode)
        f.close()


    def genCode(self):
        stateCode = []
        tokenTypeCode = []
        for isInit,isAccept,state,label in self.dfaTable.iterateStates():
            # state is a unique name, label isn't; If accepting state the label should go into the enum defintions.
            transition = "state{0}:\n".format(state)
            if isInit:
                transition += "c = start_char;\n"
            else:
                transition += "c = provider.next();\n"

            for to, transVar in self.dfaTable.iterateTransitionsFor(state):
                transition += "if (c == '{0}') goto {1};\n".format(transVar,int(to))
            

            if isAccept: # None of the previous transitions matched. If it is an accepting state, accept the string and return 
                transition += """
                                if (!isspace(c)) start_char = c; 
                                current_token_info = {{ TokenType::{0},  matched_word, filename, startedLine, startedPosition }}; 
                                return;""".format(label)
                tokenTypeCode.append("{0},\n\t".format(label))
            else:
                transition += "assert(false);" #Proper error handling soon.
            transition+="\n\n\n"

            stateCode.append(transition)
        
        methodDefinition = "".join(stateCode)
        tokenTypeDefinition = "".join(tokenTypeCode)
        return (methodDefinition,tokenTypeDefinition[0:-2])

        




        

def emit_code(tokenSpec,pathToSave):
    automataList = []
    print("Creating sub NFAs...")
    for i in tokenSpec:
        label,expr = i
        enfa = make_nfa(make_expr(expr))
        enfa.acceptState.label = label
        automataList.append(enfa)
    print("Done")
    print("Merging sub NFAs...")

    enfa = automataList[0]
    for i in automataList[1:]:
        enfa.union(i)
    print("Done")
    print("Tranforming NFA to DFA...")

    dfaTable = enfa.transitionTable.to_dfa()
    print("Done")
    print("Emitting CPP Code...")
    #draw_fa(dfaTable)
    genLexer = CPPLexer(dfaTable)
    print("Done")
    genLexer.save(pathToSave)
    







a=parse_source("C:/Users/Jan_M720/Desktop/TokenMoses.txt")
emit_code(a,"C:/Users/Jan_M720/Desktop/TestLexer.h")


"""a = make_expr("ret|re(te)*")
#a = make_expr("a|a|b*")
b = make_nfa(a)
draw_expr(a, "Expression")
t = b.transitionTable
draw_fa(t, "eNFA")
draw_fa(t.to_Estar(),"Estar") 
draw_fa(t.remove_epsilon_trans(False),"NFA")
draw_fa(t.to_dfa(False),"DFA!!")
print("END")"""











