# logicPlan.py
# ------------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


"""
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

from typing import Dict, List, Tuple, Callable, Generator, Any
import util
import sys
import logic
import game

from logic import conjoin, disjoin
from logic import PropSymbolExpr, Expr, to_cnf, pycoSAT, parseExpr, pl_true

import itertools
import copy

pacman_str = 'P'
food_str = 'FOOD'
wall_str = 'WALL'
pacman_wall_str = pacman_str + wall_str
ghost_pos_str = 'G'
ghost_east_str = 'GE'
pacman_alive_str = 'PA'
DIRECTIONS = ['North', 'South', 'East', 'West']
blocked_str_map = dict([(direction, (direction + "_blocked").upper()) for direction in DIRECTIONS])
geq_num_adj_wall_str_map = dict([(num, "GEQ_{}_adj_walls".format(num)) for num in range(1, 4)])
DIR_TO_DXDY_MAP = {'North':(0, 1), 'South':(0, -1), 'East':(1, 0), 'West':(-1, 0)}


#______________________________________________________________________________
# QUESTION 1

def sentence1() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    # Creating A, B and C symbols
    A = Expr('A')
    B = Expr('B')
    C = Expr('C')
    
    # Adding the expressions for the sentence1 in a list
    sentenses = [A | B, ~ A % (~ B | C), disjoin([~ A, ~ B, C])]
    
    # returing the conjoin of the exrpessions from the list
    return conjoin(sentenses)

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    # Creating the symbols first
    A = Expr('A')
    B = Expr('B')
    C = Expr('C')
    D = Expr('D')
    
    # Adding the given expression in a list
    sentenses = [C % (B | D), A >> ((~ B) & (~ D)) , (~ (B & (~C))) >> A, (~ D) >> C]
    
    # Returning the cnojoin from all the exression from the list
    return conjoin(sentenses)
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.

    Pacman cannot both be alive at time 0 and be born at time 0.

    Pacman is born at time 0.
    (Project update: for this question only, [0] and _t are both acceptable.)
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    # Creating the symbols with the PropSymbolExpr constructor
    PacmanAlive_1 = PropSymbolExpr('PacmanAlive_1')
    PacmanAlive_0 = PropSymbolExpr('PacmanAlive_0')
    PacmanBorn_0 = PropSymbolExpr('PacmanBorn_0')
    PacmanKilled_0 = PropSymbolExpr('PacmanKilled_0')
    
    # Creating the fisrt expression from the first sentence
    first_expr = PacmanAlive_1 % (PacmanAlive_0 & ~ PacmanKilled_0 | ~ PacmanAlive_0 & PacmanBorn_0)
    
    # Creating expression from second sentence
    second_expr = ~ (PacmanAlive_0 & PacmanBorn_0)
    
    # Creating the third sentence 
    third_expr = PacmanBorn_0
    
    # Adding the 3 expressions in a list 
    sentences = [first_expr, second_expr, third_expr]
    
    # Then coinjoin the expression from the list
    return conjoin(sentences)

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    cnf_sentence = to_cnf(sentence)
    return pycoSAT(cnf_sentence)

def findModelCheck() -> Dict[Any, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    This can be solved with a one-line return statement.
    """
    class dummyClass:
        """dummy('A') has representation A, unlike a string 'A' that has repr 'A'.
        Of note: Expr('Name') has representation Name, not 'Name'.
        """
        def __init__(self, variable_name: str = 'A'):
            self.variable_name = variable_name
        
        def __repr__(self):
            return self.variable_name
    "*** BEGIN YOUR CODE HERE ***"

    # Returning the dictionary with the dummyClass and True boolean value
    return {dummyClass('a') : True}

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    """
    "*** BEGIN YOUR CODE HERE ***"

    # if premise AND NOT conclusion is satisfiable then premise does not entail conclusion
    # if premise AND NOT conclusion is NOT satisfiable then premise entail conclusion
    
    if findModel(premise & ~ conclusion):
        return False
    
    return True
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    #Based on assignments then if the NOT inverse_statement is true
    return pl_true(~ inverse_statement, assignments)
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 2

def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single 
    Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals  ist is true.
    >>> A = PropSymbolExpr('A');
    >>> B = PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print(pl_true(atleast1,model1))
    False
    >>> model2 = {A:False, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    >>> model3 = {A:True, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    # Using disjoin (OR) so if at least one is true then the expression will be true
    # return the disjoined expr
    
    return disjoin(literals)
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    itertools.combinations may be useful here.
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    sentences = []
    
    # getting all the combinations and add the the (~expr_1 | ~expr_2) expr in the list
    # (~expr_1 | ~expr_2) means that if the expr_1 is true xor expr_2 is true or none of 
    # them are true then the expr is also true
    # then return conjoined expr of the exprs from list
    
    for expr_1, expr_2 in itertools.combinations(literals, 2):
        sentences.append(~expr_1 | ~expr_2)    

    return conjoin(sentences)
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    "*** BEGIN YOUR CODE HERE ***"
    
    sentences = []
    
    # Using the at least one method and add the exprs in the list
    disjoined_literals = disjoin(literals)
    sentences.append(disjoined_literals)

    # Using the at most one method and add them again in the list
    for expr_1, expr_2 in itertools.combinations(literals, 2):
        sentences.append(~expr_1 | ~expr_2)

    # The conjoined expr will have at least one and at most one 
    # and that means that it will return the expression that represents that Exactly one is true or not
    
    return conjoin(sentences)
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 3

def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]=None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    now, last = time, time - 1
    possible_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t
    # the if statements give a small performance boost and are required for q4 and q5 correctness
    if walls_grid[x][y+1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    
    "*** BEGIN YOUR CODE HERE ***"
    
    # pacman position at t <=> possible previous position from pacman
    return PropSymbolExpr(pacman_str, x, y, time=now) % disjoin(possible_causes)
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1
    moved_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    if walls_grid[x][y+1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin([~PropSymbolExpr(pacman_str, x, y, time=last) , ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    failed_move_causes: List[Expr] = [] # using merged variables, improves speed significantly
    auxilary_expression_definitions: List[Expr] = []
    for direction in DIRECTIONS:
        dx, dy = DIR_TO_DXDY_MAP[direction]
        wall_dir_clause = PropSymbolExpr(wall_str, x + dx, y + dy) & PropSymbolExpr(direction, time=last)
        wall_dir_combined_literal = PropSymbolExpr(wall_str + direction, x + dx, y + dy, time=last)
        failed_move_causes.append(wall_dir_combined_literal)
        auxilary_expression_definitions.append(wall_dir_combined_literal % wall_dir_clause)

    failed_move_causes_sent: Expr = conjoin([
        PropSymbolExpr(pacman_str, x, y, time=last),
        disjoin(failed_move_causes)])

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin([moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)


def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing all of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    pacphysics_sentences = []

    "*** BEGIN YOUR CODE HERE ***"

    non_outer_wall_coords_grid_exprs = []

    # for all the x, y coordinates if there is a wall then the pacman is not at x,y at time t
    for x, y in all_coords:
        pacphysics_sentences.append(PropSymbolExpr(wall_str, x, y) >> ~PropSymbolExpr(pacman_str, x, y, time=t))
    
    # Pacman is at exactly on of the outer world coordinates
    for x, y in non_outer_wall_coords:
        non_outer_wall_coords_grid_exprs.append(PropSymbolExpr(pacman_str, x, y, time=t))
    
    # Appending the expr representing exactly one
    pacphysics_sentences.append(exactlyOne(non_outer_wall_coords_grid_exprs))
    
    # Pacman takes exactly one action from all the directions
    actions_list = []
    for action in DIRECTIONS:
        actions_list.append(PropSymbolExpr(action, time=t))
    
    # Appending the exactly one
    pacphysics_sentences.append(exactlyOne(actions_list))
    
    # if sensorModel func parameter exists then append the result in the list
    if sensorModel:
        pacphysics_sentences.append(sensorModel(t, non_outer_wall_coords))
    
    # if successor Axioms func param exists and walls_grid param exists and time t > 0 then append the result of the function in list
    if successorAxioms and walls_grid and t > 0:
        pacphysics_sentences.append(successorAxioms(t, walls_grid, non_outer_wall_coords))
    
    "*** END YOUR CODE HERE ***"

    # Returning the conjoined expr
    return conjoin(pacphysics_sentences)


def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
    Given:
        - x1_y1 = (x1, y1), a potential location at time t = 1
        - x0_y0 = (x0, y0), Pacman's location at time t = 0
        - action0 = one of the four items in DIRECTIONS, Pacman's action at time t = 0
        - action1 = to ensure match with autograder solution
        - problem = an instance of logicAgents.LocMapProblem
    Note:
        - there's no sensorModel because we know everything about the world
        - the successorAxioms should be allLegalSuccessorAxioms where needed
    Return:
        - a model where Pacman is at (x1, y1) at time t = 1
        - a model where Pacman is not at (x1, y1) at time t = 1
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # We know which coords are walls:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]
    KB.append(conjoin(map_sent))

    "*** BEGIN YOUR CODE HERE ***"
    
    # Appending to KB pacphysicsAxioms func for t = 0 and t = 1 and call it with allLegalSuccessorAxioms func param
    KB.append(pacphysicsAxioms(0, all_coords, non_outer_wall_coords, walls_grid, successorAxioms=allLegalSuccessorAxioms))
    KB.append(pacphysicsAxioms(1, all_coords, non_outer_wall_coords, walls_grid, successorAxioms=allLegalSuccessorAxioms))
    
    # Adding to KB the pacmans starting position
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))
    
    # Adding action0 and action1 for time = 0 and time = 1
    KB.append(PropSymbolExpr(action0, time=0))
    KB.append(PropSymbolExpr(action1, time=1))
    
    # Model 1 is at x1,y1 at time = 1
    model_1_sentences = KB + [PropSymbolExpr(pacman_str, x1, y1, time=1)]
    model1 = findModel(conjoin(model_1_sentences))
    
    # Model 2 is NOT at x1, y1 at time = 1
    model_2_sentences = KB + [~ PropSymbolExpr(pacman_str, x1, y1, time=1)]
    model2 = findModel(conjoin(model_2_sentences))
    
    return (model1, model2)

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 4

def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), 
            range(height + 2)))
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    
    # Adding to KB the initial location of pacman
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))

    # t is tested from 0 to 49
    
    for t in range(50):
        
        non_wall_coords_exprs = []
        
        # Pacman can only be at one location from the non wall coordinates at every time step t
        for x, y in non_wall_coords:
            non_wall_coords_exprs.append(PropSymbolExpr(pacman_str, x, y, time=t))

        # Appending the exactly one
        KB.append(exactlyOne(non_wall_coords_exprs))

        # Printing the progress
        print(f'time step = {t}')
        
        
        actions_list = []
        
        # Pacaman does exactly one action every time step t
        for action in actions:
            actions_list.append(PropSymbolExpr(action, time=t))
        KB.append(exactlyOne(actions_list))

        # If timestep greater than 0 then append to KB the axiom for state at t from time step t - 1
        if t > 0:
            for x, y in non_wall_coords:
                KB.append(pacmanSuccessorAxiomSingle(x, y, t, walls_grid))
        
        # Check if there is ant satisfying model that reach the pacman's goal position
        kb_goal_sentences = KB + [PropSymbolExpr(pacman_str, xg, yg, time=t)]
        model = findModel(conjoin(kb_goal_sentences))
        
        # If there is a model then return the actions list
        if model:
            return extractActionSequence(model, actions)
        
    return []

    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls.asList()
    (x0, y0), food = problem.start
    food = food.asList()

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    
    # Starting position of pacman at time step 0
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))

    # For all the food coords, add them in the exprs in the KB
    curr_food_coords = [] 
    for x, y in food:
        curr_food_coords.append(PropSymbolExpr(food_str, x, y, time=0))

    KB.append(conjoin(curr_food_coords))
    
    # For 50 times steps
    for t in range(50):

        # Printing progress
        print(f'time step = {t}')
        
        # Pacman can have an exactlyOne possible location at time step t
        non_wall_coords_exprs = [] 
        for x, y in non_wall_coords:
            non_wall_coords_exprs.append(PropSymbolExpr(pacman_str, x, y, time=t))

        KB.append(exactlyOne(non_wall_coords_exprs))

        # Pacman takes exactly one action
        actions_list = []
        for action in actions:
            actions_list.append(PropSymbolExpr(action, time=t))
        KB.append(exactlyOne(actions_list))

        # if time step is > 0 then call pacmanSuccessorAxiomSingle (like previous question)
        if t > 0:
            for x, y in non_wall_coords:
                KB.append(pacmanSuccessorAxiomSingle(x, y, t, walls))
        
        # for every time step t append in the KB if pacman has passed from this coordinate
        # if pacman has not gone to this coordinate x, y then the food dot will still exist in time step t + 1 
        for x, y in food:
            KB.append((~PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(food_str, x, y, time=t)) >> PropSymbolExpr(food_str, x, y, time=t+1))
        
        # Goal expression is if all the food has been eaten
        goal_food_exprs = [] 
        for x, y in food:
            goal_food_exprs.append(~PropSymbolExpr(food_str, x, y, time=t))  
        
        # Check if a satisfying model exists 
        kb_goal_sentences = KB + [conjoin(goal_food_exprs)]
        model = findModel(conjoin(kb_goal_sentences))

        # If a sat model exists return the actions
        if model:
            return extractActionSequence(model, actions)
        
    return []
    
    util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 6

def localization(problem, agent) -> Generator:
    '''
    problem: a LocalizationProblem instance
    agent: a LocalizationLogicAgent instance
    '''
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    KB = []

    "*** BEGIN YOUR CODE HERE ***"
    
    # Adding to KB where the walls are and aren't
    for x, y in all_coords:
        if (x, y) in walls_list:
            KB.append(PropSymbolExpr(wall_str, x, y))
        else:
            KB.append(~PropSymbolExpr(wall_str, x, y))

    # for a total of num_timesteps
    for t in range(agent.num_timesteps):

        print(f'time step = {t}')
        
        possible_locations = []
        
        # Adding to KB the pacphysics axioms from question 3
        # pacphysicsAxioms is called with allLegalSuccessorAxioms and SLAMSensorAxioms pfunc parameters
        # for localization and mapping
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, walls_grid, sensorAxioms, allLegalSuccessorAxioms))
        
        # Spesific action for time step t
        action_t = agent.actions[t]
        
        KB.append(PropSymbolExpr(action_t, time=t))
        
        # Getting the 4 bit percept rules
        percepts = agent.getPercepts()
        rules = fourBitPerceptRules(t, percepts)
        
        KB.append(rules) 

        # Iterating over non outer wall coords
        for x, y in non_outer_wall_coords:
            
            # Checking if pacman is at x,y coordinates at time step t (Satifying assignment)
            kb_pacman_sentences = KB + [PropSymbolExpr(pacman_str, x, y, time=t)]
            if findModel(conjoin(kb_pacman_sentences)):
                possible_locations.append((x,y))
            
            # Prove if pacman is at x,y coordinates
            if entails(conjoin(KB), PropSymbolExpr(pacman_str, x, y, time=t)):
                KB.append(PropSymbolExpr(pacman_str, x, y, time=t))
                
            # Prove if pacman is NOT at x,y coordinates
            elif entails(conjoin(KB), ~PropSymbolExpr(pacman_str, x, y, time=t)):
                KB.append(~PropSymbolExpr(pacman_str, x, y, time=t))
        
        
        # Move to the nect state based on action          
        agent.moveToNextState(action_t)
        
        "*** END YOUR CODE HERE ***"
        yield possible_locations

#______________________________________________________________________________
# QUESTION 7

def mapping(problem, agent) -> Generator:
    '''
    problem: a MappingProblem instance
    agent: a MappingLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # Pacman knows that the outer border of squares are all walls
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    
    # Append the initial location of pacman to KB
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))
    
    # If the is a wall at pacman's location based on known map then add it to KB
    if known_map[pac_x_0][pac_y_0] == 1:
        KB.append(PropSymbolExpr(wall_str, pac_x_0, pac_y_0, time=0))
    
    # for a total of num_timesteps
    for t in range(agent.num_timesteps):
        
        print(f'time step = {t}')
        
        # Adding the pacphysicsAxioms result of question 3. Calling it with sensorAxioms and allLegalSuccessorAxioms func params
        # Passing known_map
        
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, sensorAxioms, allLegalSuccessorAxioms))
        
        # Getting pacman action
        action_t = agent.actions[t]
        
        KB.append(PropSymbolExpr(action_t, time=t))
        
        # Appending the KB rules based on pacman percepts
        percepts = agent.getPercepts()
        rules = fourBitPerceptRules(t, percepts)
        
        KB.append(rules)
        
        
        for x, y in non_outer_wall_coords:
            
            # Proving if there is a wall at x, y using entail
            if entails(conjoin(KB), PropSymbolExpr(wall_str, x, y)):
                KB.append(PropSymbolExpr(wall_str, x, y, time=t)) 
                known_map[x][y] = 1
            
            # Proving if there is NOT a wall at x, y using entail
            elif entails(conjoin(KB), ~PropSymbolExpr(wall_str, x, y)):
                KB.append(~PropSymbolExpr(wall_str, x, y, time=t))
                known_map[x][y] = 0
        
        # moving to next state
        agent.moveToNextState(action_t)
        
        "*** END YOUR CODE HERE ***"
        yield known_map

#______________________________________________________________________________
# QUESTION 8

def slam(problem, agent) -> Generator:
    '''
    problem: a SLAMProblem instance
    agent: a SLAMLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # We know that the outer_coords are all walls.
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"
    
    # Combining the implementation of QUESTION 6 and QUESTION 7
    
    
    # Append pacman starting position
    KB.append(PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time=0))
    
    # if there is a wall based on the known map then append the position expr in KB
    if known_map[pac_x_0][pac_y_0] == 1:
        KB.append(PropSymbolExpr(wall_str, pac_x_0, pac_y_0, time=0))

    # for a total of num_timesteps timesteps
    for t in range(agent.num_timesteps):
        
        # prining the progress
        print(f'time step = {t}')
        
        possible_locations = []
        
        # calling pacphysicsAxioms with SLAMSensorAxioms and SLAMSuccessorAxioms as func params for localization and mapping
        KB.append(pacphysicsAxioms(t, all_coords, non_outer_wall_coords, known_map, SLAMSensorAxioms, SLAMSuccessorAxioms))
        
        # getting the pacman action based on time step t
        action_t = agent.actions[t]
        
        KB.append(PropSymbolExpr(action_t, time=t))
        
        # getting the rules calling numAdjWallsPerceptRules for this question
        percepts = agent.getPercepts()
        rules = numAdjWallsPerceptRules(t, percepts)
        
        KB.append(rules) 

        for x, y in non_outer_wall_coords:
            
            # Proving if there is a wall at coordinates x, y
            if entails(conjoin(KB), PropSymbolExpr(wall_str, x, y)):
                KB.append(PropSymbolExpr(wall_str, x, y, time=t)) 
                known_map[x][y] = 1
            
            # Proving if there is not a wall at x, y
            elif entails(conjoin(KB), ~PropSymbolExpr(wall_str, x, y)):
                KB.append(~PropSymbolExpr(wall_str, x, y, time=t))
                known_map[x][y] = 0
            
            # Checking if there is a satisfying model for pacman to be at coordinates x, y
            kb_pacman_sentences = KB + [PropSymbolExpr(pacman_str, x, y, time=t)]
            if findModel(conjoin(kb_pacman_sentences)):
                possible_locations.append((x,y))
            
            # Proving if pacman is at coordinates x, y at time step t
            if entails(conjoin(KB), PropSymbolExpr(pacman_str, x, y, time=t)):
                KB.append(PropSymbolExpr(pacman_str, x, y, time=t))
            
            # Proving if pacman is not at coordinates x, y at time step t
            elif entails(conjoin(KB), ~PropSymbolExpr(pacman_str, x, y, time=t)):
                KB.append(~PropSymbolExpr(pacman_str, x, y, time=t))
   
        
        # moving to next state
        agent.moveToNextState(action_t)        
        
        "*** END YOUR CODE HERE ***"
        yield (known_map, possible_locations)


# Abbreviations
plp = positionLogicPlan
loc = localization
mp = mapping
flp = foodLogicPlan
# Sometimes the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)

#______________________________________________________________________________
# Important expression generating functions, useful to read for understanding of this project.


def sensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (
                PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time = t)
        all_percept_exprs.append(percept_unit_clause % disjoin(percept_exprs))

    return conjoin(all_percept_exprs + combo_var_def_exprs)


def fourBitPerceptRules(t: int, percepts: List) -> Expr:
    """
    Localization and Mapping both use the 4 bit sensor, which tells us True/False whether
    a wall is to pacman's north, south, east, and west.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 4, "Percepts must be a length 4 list."

    percept_unit_clauses = []
    for wall_present, direction in zip(percepts, DIRECTIONS):
        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        if not wall_present:
            percept_unit_clause = ~PropSymbolExpr(blocked_str_map[direction], time=t)
        percept_unit_clauses.append(percept_unit_clause) # The actual sensor readings
    return conjoin(percept_unit_clauses)


def numAdjWallsPerceptRules(t: int, percepts: List) -> Expr:
    """
    SLAM uses a weaker numAdjWallsPerceptRules sensor, which tells us how many walls pacman is adjacent to
    in its four directions.
        000 = 0 adj walls.
        100 = 1 adj wall.
        110 = 2 adj walls.
        111 = 3 adj walls.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 3, "Percepts must be a length 3 list."

    percept_unit_clauses = []
    for i, percept in enumerate(percepts):
        n = i + 1
        percept_literal_n = PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t)
        if not percept:
            percept_literal_n = ~percept_literal_n
        percept_unit_clauses.append(percept_literal_n)
    return conjoin(percept_unit_clauses)


def SLAMSensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        blocked_dir_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        all_percept_exprs.append(blocked_dir_clause % disjoin(percept_exprs))

    percept_to_blocked_sent = []
    for n in range(1, 4):
        wall_combos_size_n = itertools.combinations(blocked_str_map.values(), n)
        n_walls_blocked_sent = disjoin([
            conjoin([PropSymbolExpr(blocked_str, time=t) for blocked_str in wall_combo])
            for wall_combo in wall_combos_size_n])
        # n_walls_blocked_sent is of form: (N & S) | (N & E) | ...
        percept_to_blocked_sent.append(
            PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t) % n_walls_blocked_sent)

    return conjoin(all_percept_exprs + combo_var_def_exprs + percept_to_blocked_sent)


def allLegalSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = pacmanSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)


def SLAMSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = SLAMSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)

#______________________________________________________________________________
# Various useful functions, are not needed for completing the project but may be useful for debugging


def modelToString(model: Dict[Expr, bool]) -> str:
    """Converts the model to a string for printing purposes. The keys of a model are 
    sorted before converting the model to a string.
    
    model: Either a boolean False or a dictionary of Expr symbols (keys) 
    and a corresponding assignment of True or False (values). This model is the output of 
    a call to pycoSAT.
    """
    if model == False:
        return "False" 
    else:
        # Dictionary
        modelList = sorted(model.items(), key=lambda item: str(item[0]))
        return str(modelList)


def extractActionSequence(model: Dict[Expr, bool], actions: List) -> List:
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[2]":True, "P[3,4,0]":True, "P[3,3,0]":False, "West[0]":True, "GhostScary":True, "West[2]":False, "South[1]":True, "East[0]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print(plan)
    ['West', 'South', 'North']
    """
    plan = [None for _ in range(len(model))]
    for sym, val in model.items():
        parsed = parseExpr(sym)
        if type(parsed) == tuple and parsed[0] in actions and val:
            action, _, time = parsed
            plan[time] = action
    #return list(filter(lambda x: x is not None, plan))
    return [x for x in plan if x is not None]


# Helpful Debug Method
def visualizeCoords(coords_list, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    for (x, y) in itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)):
        if (x, y) in coords_list:
            wallGrid.data[x][y] = True
    print(wallGrid)


# Helpful Debug Method
def visualizeBoolArray(bool_arr, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    wallGrid.data = copy.deepcopy(bool_arr)
    print(wallGrid)

class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()
        
    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()
