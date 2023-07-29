# multiAgents.py
# --------------
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


from util import manhattanDistance
from game import Directions
import random, util

from game import Agent
from pacman import GameState

class ReflexAgent(Agent):
    """
    A reflex agent chooses an action at each choice point by examining
    its alternatives via a state evaluation function.

    The code below is provided as a guide.  You are welcome to change
    it in any way you see fit, so long as you don't touch our method
    headers.
    """


    def getAction(self, gameState: GameState):
        """
        You do not need to change this method, but you're welcome to.

        getAction chooses among the best options according to the evaluation function.

        Just like in the previous project, getAction takes a GameState and returns
        some Directions.X for some X in the set {NORTH, SOUTH, WEST, EAST, STOP}
        """
        # Collect legal moves and successor states
        legalMoves = gameState.getLegalActions()

        # Choose one of the best actions
        scores = [self.evaluationFunction(gameState, action) for action in legalMoves]
        bestScore = max(scores)
        bestIndices = [index for index in range(len(scores)) if scores[index] == bestScore]
        chosenIndex = random.choice(bestIndices) # Pick randomly among the best

        "Add more of your code here if you want to"

        return legalMoves[chosenIndex]

    def evaluationFunction(self, currentGameState: GameState, action):
        """
        Design a better evaluation function here.

        The evaluation function takes in the current and proposed successor
        GameStates (pacman.py) and returns a number, where higher numbers are better.

        The code below extracts some useful information from the state, like the
        remaining food (newFood) and Pacman position after moving (newPos).
        newScaredTimes holds the number of moves that each ghost will remain
        scared because of Pacman having eaten a power pellet.

        Print out these variables to see what you're getting, then combine them
        to create a masterful evaluation function.
        """
        # Useful information you can extract from a GameState (pacman.py)
        successorGameState = currentGameState.generatePacmanSuccessor(action)
        newPos = successorGameState.getPacmanPosition()
        newFood = successorGameState.getFood()
        newGhostStates = successorGameState.getGhostStates()
        newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]

        "*** YOUR CODE HERE ***"
        
        # Calculating an evaluation value
        evaluation = 0
        
        # For every ghost in new state
        for state in newGhostStates:
            position = state.getPosition()
            
            # Get manhattan distance between pacman and ghost
            pacman_ghost_dist = manhattanDistance(newPos, position)
            
            # if any ghost is too close (next to pacman) then decrease evaluation
            if pacman_ghost_dist < 2:
                evaluation -= 3
        
        food_list = newFood.asList()
        
        # If the new position of pacman has any food dot then increase evaluation
        if newPos in food_list:
            evaluation += 2
     
        dist_food = [] 
        for food_pos in food_list:
            dist_food.append(manhattanDistance(newPos, food_pos))
        
        # The closer the food the better the evaluation value will be so pacman can eat food dots
        if (len(dist_food)):
            evaluation += 1.0 / min(dist_food)
        
        # Also checking for capsule dots
        capsules_dist_list = []
        for capsule in successorGameState.getCapsules():
            capsules_dist_list.append(manhattanDistance(newPos, capsule))

        # if there is any capsule dot then the closer it is the better evaluation pacman will have for this state
        if (len(capsules_dist_list)):
            evaluation += 1 / min(capsules_dist_list)
            
        return successorGameState.getScore() + evaluation

def scoreEvaluationFunction(currentGameState: GameState):
    """
    This default evaluation function just returns the score of the state.
    The score is the same one displayed in the Pacman GUI.

    This evaluation function is meant for use with adversarial search agents
    (not reflex agents).
    """
    return currentGameState.getScore()

class MultiAgentSearchAgent(Agent):
    """
    This class provides some common elements to all of your
    multi-agent searchers.  Any methods defined here will be available
    to the MinimaxPacmanAgent, AlphaBetaPacmanAgent & ExpectimaxPacmanAgent.

    You *do not* need to make any changes here, but you can if you want to
    add functionality to all your adversarial search agents.  Please do not
    remove anything, however.

    Note: this is an abstract class: one that should not be instantiated.  It's
    only partially specified, and designed to be extended.  Agent (game.py)
    is another abstract class.
    """

    def __init__(self, evalFn = 'scoreEvaluationFunction', depth = '2'):
        self.index = 0 # Pacman is always agent index 0
        self.evaluationFunction = util.lookup(evalFn, globals())
        self.depth = int(depth)

class MinimaxAgent(MultiAgentSearchAgent):
    """
    Your minimax agent (question 2)
    """
    
    # Method for max nodes
    def max_value(self, state: GameState, depth, agent):
        
        # depth is 0 or state is win or state is lose then return evaluation number and None action
        if depth == 0 or state.isWin() or state.isLose():
            return self.evaluationFunction(state), None
        
        # Initialize max to -infinity (large small number)
        max_evaluation = float('-inf'), None
        
        # Pacmans legal actions
        actions = state.getLegalActions(agent)
        
        # For every pacman action
        for action in actions:
            successor = state.generateSuccessor(agent, action)
            evaluation = self.min_value(successor, depth, 1)
            
            # If new evaluation is bigger than previous evaluation then store the new evaluation and the action
            if evaluation[0] > max_evaluation[0]:
                max_evaluation = evaluation[0], action
        
        return max_evaluation


    # Method for min nodes
    def min_value(self, state: GameState, depth, agent):
        
        # If at last depth then (i decrease the max depth) then return evaluation number, the action (None action for leaf node)
        if depth == 0 or state.isWin() or state.isLose():
            return self.evaluationFunction(state), None

        # Initialize min to infinity (large big number)
        min_evaluation = float('inf'), None
            
        actions = state.getLegalActions(agent)
        
        # For every ghost action (agent 0 is pacman and agent > 0 is every ghost agent)
        for action in actions:
            successor = state.generateSuccessor(agent, action)
            
            # If at last ghost then call max for pacman
            if agent == state.getNumAgents() - 1:
                evaluation = self.max_value(successor, depth - 1, 0)
                
                if evaluation[0] < min_evaluation[0]:
                    min_evaluation = evaluation[0], action
                    
            # Min for the next ghost
            else:
                evaluation = self.min_value(successor, depth, agent+1)
                
                # If new evaluation is smaller than previous evaluation then store the new evaluation and the action
                if evaluation[0] < min_evaluation[0]:
                    min_evaluation = evaluation[0], action
        
        return min_evaluation
                    
    
    def getAction(self, gameState: GameState):
        """
        Returns the minimax action from the current gameState using self.depth
        and self.evaluationFunction.

        Here are some method calls that might be useful when implementing minimax.

        gameState.getLegalActions(agentIndex):
        Returns a list of legal actions for an agent
        agentIndex=0 means Pacman, ghosts are >= 1

        gameState.generateSuccessor(agentIndex, action):
        Returns the successor game state after an agent takes an action

        gameState.getNumAgents():
        Returns the total number of agents in the game

        gameState.isWin():
        Returns whether or not the game state is a winning state

        gameState.isLose():
        Returns whether or not the game state is a losing state
        """
        "*** YOUR CODE HERE ***"
        
        # Call Max first (like theory). Returning value, action
        # Value is important for the min max methods but action is important for the this method to return
        value, action = self.max_value(gameState, self.depth, 0)
        return action
    
        util.raiseNotDefined()

class AlphaBetaAgent(MultiAgentSearchAgent):
    """
    Your minimax agent with alpha-beta pruning (question 3)
    """
    
    # Same code with minimax but now checking for a, b values so paths can be pruned
    
    def max_value(self, state: GameState, depth, agent, a, b):
        
        # leaf node or win state or lose state
        if depth == 0 or state.isWin() or state.isLose():
            return self.evaluationFunction(state), None
        
        max_evaluation = float('-inf'), None
        
        actions = state.getLegalActions(agent)
        
        # Every action
        for action in actions:
            successor = state.generateSuccessor(agent, action)
            evaluation = self.min_value(successor, depth, 1, a, b)
            
            if evaluation[0] > max_evaluation[0]:
                max_evaluation = evaluation[0], action
            
            # If the evaluation is bigger than b then no need to search anymore because min has already found a better value to pick
            if evaluation[0] > b:
                return max_evaluation
            
            # updating a with the max evaluation if found so min can prune       
            a = max(a, evaluation[0])
                
        return max_evaluation



    def min_value(self, state: GameState, depth, agent, a, b):
        
        # leaf node or win state or lose state
        if depth == 0 or state.isWin() or state.isLose():
            return self.evaluationFunction(state), None
    
        min_evaluation = float('inf'), None
            
        actions = state.getLegalActions(agent)
        
        for action in actions:
            successor = state.generateSuccessor(agent, action)
            
            if agent == state.getNumAgents() - 1:
                evaluation = self.max_value(successor, depth - 1, 0, a, b)
                
                if evaluation[0] < min_evaluation[0]:
                    min_evaluation = evaluation[0], action
                
                if evaluation[0] < a:
                    return min_evaluation
            
            else:
                evaluation = self.min_value(successor, depth, agent+1, a, b)
                
                if evaluation[0] < min_evaluation[0]:
                    min_evaluation = evaluation[0], action
                    
                # If the evaluation is smaller than a then no need to search anymore because max has already found a better value to pick
                if evaluation[0] < a:
                    return min_evaluation
            
            # Keep b updated with min value of evaluation
            b = min(b, evaluation[0])
        
        return min_evaluation
    
    

    def getAction(self, gameState: GameState):
        """
        Returns the minimax action using self.depth and self.evaluationFunction
        """
        "*** YOUR CODE HERE ***"
        
        # Call Max first. Returning value, action
        # action value is important thats why min max methods returns those values
        value, action = self.max_value(gameState, self.depth, 0, float('-inf'), float('inf'))
        
        return action
        util.raiseNotDefined()
        
        

class ExpectimaxAgent(MultiAgentSearchAgent):
    """
      Your expectimax agent (question 4)
    """
    
    # Max value method same as minimax algorithm
    def max_value(self, state: GameState, depth, agent):
        
        if depth == 0 or state.isWin() or state.isLose():
            return self.evaluationFunction(state), None
        
        max_evaluation = float('-inf'), None
        
        actions = state.getLegalActions(agent)
        
        for action in actions:
            successor = state.generateSuccessor(agent, action)
            evaluation = self.expectimax(successor, depth, 1)
            
            if evaluation[0] > max_evaluation[0]:
                max_evaluation = evaluation[0], action
        
        return max_evaluation


    # Same as min value from minimax but the evaluation is the average of all the ghost actions
    def expectimax(self, state: GameState, depth, agent):
        
        if depth == 0 or state.isWin() or state.isLose():
            return self.evaluationFunction(state), None

        sum_eval = 0
            
        actions = state.getLegalActions(agent)
        
        for action in actions:
            successor = state.generateSuccessor(agent, action)
            
            if agent == state.getNumAgents() - 1:
                evaluation = self.max_value(successor, depth - 1, 0)
            
            else:
                evaluation = self.expectimax(successor, depth, agent + 1)

            sum_eval += evaluation[0] / len(actions)  # divide with number of actions for average
        
        # Gost actions are not important and ghost action is randomly chosen because average sum evaluation is returned    
        return sum_eval, None
    
    

    def getAction(self, gameState: GameState):
        """
        Returns the expectimax action using self.depth and self.evaluationFunction

        All ghosts should be modeled as choosing uniformly at random from their
        legal moves.
        """
        "*** YOUR CODE HERE ***"
        
        # Call for max agent 0
        value, action = self.max_value(gameState, self.depth, 0)
        
        return action
       
       
def betterEvaluationFunction(currentGameState: GameState):
    """
    Your extreme ghost-hunting, pellet-nabbing, food-gobbling, unstoppable
    evaluation function (question 5).

    DESCRIPTION: <write something here so we know what you did>
    """
    "*** YOUR CODE HERE ***"
    
    # Calculating evaluation value
    evaluation = 0
    pacman_position = currentGameState.getPacmanPosition()
    
    # For every ghost calculate pacman - ghost distance
    # Decrease evaluation the closer all the ghosts are
    for ghost_position in currentGameState.getGhostPositions():
        pacman_ghost_dist = manhattanDistance(pacman_position, ghost_position)
        evaluation -= 1 / pacman_ghost_dist if pacman_ghost_dist > 0 else 0
    
    
    # For every legal action from the current state check if the next state has any food in the new pacman position
    # If there is food in the new position based on any action then increase value by 3
    for action in currentGameState.getLegalActions():
        
        nextGameState = currentGameState.generatePacmanSuccessor(action)
        
        next_pacman_pos = nextGameState.getPacmanPosition()
        
        if next_pacman_pos in nextGameState.getFood().asList():
            evaluation += 3     
            break
    
    
    #Calculating for every ghost sum of scared timers
    newGhostStates = currentGameState.getGhostStates()
    newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]
    
    scared_sum_timer = 0
    for scared_timer in newScaredTimes:
        scared_sum_timer += scared_timer
    
    # Add all ghosts scared timers in evaluation so pacman can eat even more when ghosts are in scared mode
    evaluation += scared_sum_timer
    
    food_list = currentGameState.getFood().asList()
    
    # List with all the distances between pacman and food dots
    food_list_dist = [] 
    for food_pos in food_list:
        food_list_dist.append(manhattanDistance(pacman_position, food_pos))
    
    # If there are any food dots AND scared timer is still active and bigger than 2 eat even more dots (add more in evaluation value)
    # else just add in evaluation a value based on the minimum food distance
    if (len(food_list_dist)):
        if (scared_sum_timer > 2):
            evaluation += 2 * scared_sum_timer / min(food_list_dist)
        else:
            evaluation += 4 / min(food_list_dist)
    
    # All capsules distance from pacman in a list
    capsules_dist_list = []
    for capsule in currentGameState.getCapsules():
        capsules_dist_list.append(manhattanDistance(pacman_position, capsule))
    
    # The closer the capsule the better for pacman so it can eat capsule and eat dots easier
    if (len(capsules_dist_list)):
        evaluation += 1 / min(capsules_dist_list)
    
    
    return currentGameState.getScore() + evaluation
    util.raiseNotDefined()

# Abbreviation
better = betterEvaluationFunction
