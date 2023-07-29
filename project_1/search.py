# search.py
# ---------
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
In search.py, you will implement generic search algorithms which are called by
Pacman agents (in searchAgents.py).
"""

import util

class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the search problem.
        """
        util.raiseNotDefined()

    def isGoalState(self, state):
        """
          state: Search state

        Returns True if and only if the state is a valid goal state.
        """
        util.raiseNotDefined()

    def getSuccessors(self, state):
        """
          state: Search state

        For a given state, this should return a list of triples, (successor,
        action, stepCost), where 'successor' is a successor to the current
        state, 'action' is the action required to get there, and 'stepCost' is
        the incremental cost of expanding to that successor.
        """
        util.raiseNotDefined()

    def getCostOfActions(self, actions):
        """
         actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.
        The sequence must be composed of legal moves.
        """
        util.raiseNotDefined()

def tinyMazeSearch(problem):
    """
    Returns a sequence of moves that solves tinyMaze.  For any other maze, the
    sequence of moves will be incorrect, so only use this for tinyMaze.
    """
    from game import Directions
    s = Directions.SOUTH
    w = Directions.WEST
    return  [s, s, w, s, w, w, s, w]


# Class State that stores 
# --> node of pacman
# --> path list is the list of all actions that pacman has to do to get there
# --> total cost from start to current node that pacman is (only for search algorithms that use cost)
class State:
     
    def __init__(self, node, path_list, cost = 0):
        self.node = node
        self.path_list = path_list
        self.cost = cost
    
    def get_node(self):
        return self.node
    
    def get_path(self):
        return self.path_list

    def get_cost(self):
        return self.cost


def depthFirstSearch(problem: SearchProblem):
    """
    Search the deepest nodes in the search tree first.

    Your search algorithm needs to return a list of actions that reaches the
    goal. Make sure to implement a graph search algorithm.

    To get started, you might want to try some of these simple commands to
    understand the search problem that is being passed in:

    print("Start:", problem.getStartState())
    print("Is the start a goal?", problem.isGoalState(problem.getStartState()))
    print("Start's successors:", problem.getSuccessors(problem.getStartState()))
    """
    "*** YOUR CODE HERE ***"

    # Closed is the set for explored (expanded) nodes
    closed = set()

    # Get pacman start state
    start = problem.getStartState()

    # DFS uses a stack fringe
    stack = util.Stack()
    
    # Inserting the first state into stack
    stack.push(State(start, []))

    # While stack is not empty
    while not stack.isEmpty():

        # Get the next state from the stack
        next_state = stack.pop()
        
        # Get node and path list from the class state
        node = next_state.get_node()
        path_list = next_state.get_path()

        # If this node is the goal node then returning the path list 
        if problem.isGoalState(node):
            return path_list

        # If node is not in the explored set then add it 
        if node not in closed:
            closed.add(node)
            
            # Get successors for this node and add the new States into stack (new node and all the actions)
            # Cost is not needed in DFS
            for succ, action, cost in problem.getSuccessors(node):
                stack.push(State(succ, path_list + [action]))

    util.raiseNotDefined()

def breadthFirstSearch(problem: SearchProblem):
    """Search the shallowest nodes in the search tree first."""
    "*** YOUR CODE HERE ***"

    # Closed is the set for explored (expanded) nodes
    closed = set()

    # Get pacman start state
    start = problem.getStartState()

    # BFS uses a queue fringe
    queue = util.Queue()

    # Inserting the first state into queue
    queue.push(State(start, []))

    # While queue is not empty
    while not queue.isEmpty():

        # Get the next state from the queue
        next_state = queue.pop()
        
        # Get node and path list from the class state
        node = next_state.get_node()
        path_list = next_state.get_path()

        # If this node is the goal node then returning the path list 
        if problem.isGoalState(node):
            return path_list

        # If node is not in the explored set then add it 
        if node not in closed:
            closed.add(node)
            
            # Get successors for this node and add the new States into queue (new node and all the actions)
            # Cost is not needed in BFS
            for succ, action, cost in problem.getSuccessors(node):
                queue.push(State(succ, path_list + [action]))
   
    util.raiseNotDefined()

def uniformCostSearch(problem: SearchProblem):
    """Search the node of least total cost first."""
    "*** YOUR CODE HERE ***"

    # Closed is the set for explored (expanded) nodes
    closed = set()

    # Get pacman start state
    start = problem.getStartState()

    # UCS uses a priority queue fringe
    pq = util.PriorityQueue()

    # Inserting the first state into the priority queue
    pq.push(State(start, [], 0), 0)

    # While priority queue is not empty
    while not pq.isEmpty():

        # Get next state
        next_state = pq.pop()

        # Get node, path list and total cost from the class State
        node = next_state.get_node()
        path_list = next_state.get_path()
        cost = next_state.get_cost()
        
        # IF this node is the goal state then return the path list that contains the pacman actions
        if problem.isGoalState(node):
            return path_list
        
        # If node is not in the explored set then add it 
        if node not in closed:
            closed.add(node)

            # Get successors for this node and add the new States into the priority queue (new node, all the actions and the total cost)
            for succ, action, succ_cost in problem.getSuccessors(node):
                path_cost = cost + succ_cost

                # Priority queue based on path cost value
                pq.push(State(succ, path_list + [action], path_cost), path_cost)

    util.raiseNotDefined()

def nullHeuristic(state, problem=None):
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0

def aStarSearch(problem: SearchProblem, heuristic=nullHeuristic):
    """Search the node that has the lowest combined cost and heuristic first."""
    "*** YOUR CODE HERE ***"

    # Closed is the set for explored (expanded) nodes
    closed = set()

    # Get pacman start state
    start = problem.getStartState()
    
    # A* uses a priority queue fringe (based on fn value)
    pq = util.PriorityQueue()

    # Inserting the first state into the priority queue
    pq.push(State(start, [], 0), 0)

    # While priority queue is not empty
    while not pq.isEmpty():

        # Get next state
        next_state = pq.pop()

        # Get node, path list and total cost from the class State
        node = next_state.get_node()
        path_list = next_state.get_path()
        cost = next_state.get_cost()
        
        # If this node is the goal state then return the path list that contains the pacman actions
        if problem.isGoalState(node):
            return path_list
        
        # If node is not in the explored set then add it 
        if node not in closed:
            closed.add(node)

            # Get successors for this node and add the new States into the priority queue (new node, all the actions and the total cost)
            for succ, action, succ_cost in problem.getSuccessors(node):
                path_cost = cost + succ_cost

                # Calculate fn heuristic value
                fn = path_cost + heuristic(succ, problem)

                # Priotiry queue based on fn value
                pq.push(State(succ, path_list + [action], path_cost), fn)

    util.raiseNotDefined()


# Abbreviations
bfs = breadthFirstSearch
dfs = depthFirstSearch
astar = aStarSearch
ucs = uniformCostSearch
