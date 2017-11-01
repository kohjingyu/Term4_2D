package sat;

import immutable.ImList;
import immutable.ImMap;

import sat.env.*;
import sat.formula.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Stack;

/*
Solver for 2-SAT problems. It makes use of Strongly Connected Components property and the fact that (A OR B) == (~A --> B).
The strongly connected components are generated using Kosaraju's algorithm.
If a literal and its negation exist in the same strongly connected component, the 2-SAT is unsatisfiable.
Otherwise it is satisfiable
 */

public class Graph {
	private HashMap<Literal, ArrayList<Literal>> adj = new HashMap<>(); // Adjacency list
	private HashMap<Literal, Literal> parent = new HashMap<>();
	private HashMap<Literal, Bool> satisfiability = new HashMap<>();
	private ArrayList<HashMap<Literal, Bool>> SCC = new ArrayList<>(); // All vertices in the graph
	private Stack<Literal> S = new Stack<>();
	private ArrayList<Literal> singleClause = new ArrayList<>();
	private boolean satisfiable = true; // Assume satisfiable

	public Graph(Formula formula) {
		for(Clause c : formula.getClauses()) {
			if(c.size() > 2) {
				System.out.println("Not a 2SAT problem!");
				break;
			}
			else if(c.size() == 0) {
				// Trivial case: false
				satisfiable = false;
				break;
			}
			else if(c.size() == 1) {
				//Clause (lit) is equivalent to Clause (lit, lit)
				Literal lit = c.chooseLiteral();
				Literal nLit = lit.getNegation();
				// Add vertex to the graph
				satisfiability.put(lit,null);
				satisfiability.put(nLit,null);
				
				//Add edge !lit to lit
				ArrayList<Literal> litAdj = adj.get(nLit);
				if (litAdj == null){
					litAdj = new ArrayList<Literal>();
				}
				litAdj.add(lit);
				adj.put(nLit, litAdj);
			}
			else {
				Iterator<Literal> iterator = c.iterator();

				Literal firstLit = iterator.next();
				Literal nFirstLit = firstLit.getNegation();
				Literal secondLit = iterator.next();
				Literal nSecondLit = secondLit.getNegation();

				// Add literals to vertex array
				satisfiability.putIfAbsent(firstLit, null);
				satisfiability.putIfAbsent(nFirstLit, null);
				satisfiability.putIfAbsent(secondLit, null);
				satisfiability.putIfAbsent(nSecondLit, null);
				

				// For a clause (a OR b)
				// Add edges ~a -> b and ~b -> a for each clause to the adjacency hash map
				ArrayList<Literal> firstLitAdj = adj.get(nFirstLit);
				ArrayList<Literal> secondLitAdj = adj.get(nSecondLit);

				// If the vertex has edges already, append. If it doesn't, initiate the ArrayList and append
				if(firstLitAdj == null) {
					firstLitAdj = new ArrayList<>();
				}
				firstLitAdj.add(secondLit);

				if(secondLitAdj == null) {
					secondLitAdj = new ArrayList<>();
				}
				secondLitAdj.add(firstLit);

				adj.put(nFirstLit, firstLitAdj);
				adj.put(nSecondLit, secondLitAdj);
			}
		}
	}
	//Constructor for cloning a graph with the same vertex
	public Graph(HashMap<Literal, Bool> satisfiability){
		this.satisfiability = satisfiability;
	}

	public HashMap<Variable, Bool> solve(){
		// Not satisfiable - due to trivial case of empty clauses
		if(satisfiable == false) {
			return null;
		}

		generateSCC();
		//Reverse topological order --> From high to low
		for (int i = SCC.size() - 1; i >= 0 ; i--) {
			HashMap<Literal, Bool> innerSCC = SCC.get(i);
			for (Literal lit : innerSCC.keySet()) {
				//Check if the Literal is already marked
				if (satisfiability.get(lit) == null) {
					//Check for contradiction
					if (innerSCC.containsKey(lit.getNegation())) {
						satisfiable = false;
						return null;
					} else {
						//Mark Literal as true and !Literal as false
						satisfiability.put(lit, Bool.TRUE);
						satisfiability.put(lit.getNegation(), Bool.FALSE);
					}
				}
			}
		}
		//If no contradiction occurs, it is satisfiable
		satisfiable = true;

		// Process results
		HashMap<Variable, Bool> posLitResults = new HashMap<Variable, Bool>();
		for(Literal lit : satisfiability.keySet()) {
			if(lit instanceof PosLiteral) {
				posLitResults.put(lit.getVariable(), satisfiability.get(lit));
			}
		}

		return posLitResults;
	}
	
	
	//Depth-First Search recursive.
	//Counter is used during SCC DFS to separate SCC into several index in the array list
	public void DFS_visit(Graph graph, Literal s, boolean isSCC) {
		if (isSCC) { //Check if we are finding SCC
			HashMap<Literal, Bool> innerSCC = SCC.get(SCC.size() - 1); //get the hashmap for the SCC
			innerSCC.put(s, Bool.UNDEFINED); //insert literal to the hashmap
		}

		ArrayList<Literal> neighbours = graph.getAdj().get(s); //Get the array list containing neighbours
		if (neighbours == null){ //If there are no neighbours, end.
			if (!S.contains(s) && !isSCC) {
				S.push(s);
			}
			return;
		}

		// Perform DFS on neighbours
		for(Literal v : neighbours) {
			if(graph.getParent().get(v) == null) { //If the literal is already traversed, do nothing.
				graph.getParent().put(v, s);
				DFS_visit(graph, v, isSCC);
			}
		}
		//Generate stack based on DFS finish time
		if (!S.contains(s) && !isSCC) {
			S.push(s);
		}
	}

	// Depth-First Search implementation.
	// isSCC checks if this is normal DFS or DFS to find SCC
	public void DFS(Graph graph, boolean isSCC) {
		for(Literal s : this.satisfiability.keySet()) {
			if(this.parent.get(s) == null) {
				this.parent.put(s, s);
				DFS_visit(graph, s, isSCC);
			}

			//Generate stack based on DFS finish time
			if (!S.contains(s) && !isSCC) {
				S.push(s);
			}
		}
		
	}
	
	public Graph getTranspose(){
		//Transpose the graph by flipping the direction of the edges
		Graph transposedGraph = new Graph(this.satisfiability);
		// Get the adjacency list of the transposed graph
		HashMap<Literal, ArrayList<Literal>> adjTranspose = transposedGraph.getAdj(); 
		// Traverse all vertices
		for (Literal lit1 : this.satisfiability.keySet()){ 
			ArrayList<Literal> neighbours = this.adj.get(lit1); //get List containing literals adjacent to lit1

			// If this vertex has any neighbours, add them to the transposed graph as vertices
			if (neighbours != null) {
				// Iterate through neighbours
				for (Literal lit2 : neighbours) { 
					// get the list storing the adjacent literals of lit2
					ArrayList<Literal> lit2adj = adjTranspose.get(lit2);
					if (lit2adj == null) { //If it doesn't exist, initialise
						lit2adj = new ArrayList<>();
					}

					lit2adj.add(lit1);
					adjTranspose.put(lit2, lit2adj);
				}
			}
		}
		return transposedGraph;
	}
	
	public void generateSCC(){ //Create Strongly Connected Component
		//Start DFS on current graph to generate finish time.
		this.DFS(this, false);
		Graph transposedGraph = this.getTranspose();
		//Clear SCC and Parent for second DFS
		SCC.clear();
		parent.clear();
		//Traverse through the vertex in topological order of graph G. Done by popping from DFS finish-time stack
		while (!S.empty()){
			Literal v = S.pop();
			if (!transposedGraph.getParent().containsKey(v)) {
				transposedGraph.getParent().put(v, v);
				SCC.add(new HashMap<Literal, Bool>()); //Allocate space for next SCC
				DFS_visit(transposedGraph, v, true);
			}
		}
	}
	

	public HashMap<Literal, ArrayList<Literal>> getAdj(){
		return this.adj;
	}

	public HashMap<Literal, Literal> getParent() {
		return this.parent;
	}

	public void display() {
		// Display the graph as an adjacency list
		for(Literal lit : adj.keySet()) {
			System.out.print(lit + ": ");

			for(Literal v : adj.get(lit)) {
				System.out.print(v + ", ");
			}
			System.out.println();
		}
	}
}

