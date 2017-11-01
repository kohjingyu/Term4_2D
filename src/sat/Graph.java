package sat;

import immutable.ImList;
import immutable.ImMap;

import sat.env.Bool;
import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;

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
	public HashMap<Literal, ArrayList<Literal>> adj = new HashMap<>(); // Adjacency list
	public HashMap<Literal, Literal> parent = new HashMap<>();
	private HashMap<Literal, Boolean> satisfiability = new HashMap<>();
	private ArrayList<HashMap<Literal, Boolean>> SCC = new ArrayList<>(); // All vertices in the graph
	private Stack<Literal> S = new Stack<>();
	private ArrayList<Literal> singleClause = new ArrayList<>();
	private boolean satisfiable;

	public Graph(Formula formula) {
		for(Clause c : formula.getClauses()) {
			if(c.size() > 2) {
				System.out.println("Not a 2SAT problem!");
				break;
			}
			else if(c.size() == 0) {
				// Trivial case: false
				satisfiable = false;
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
	public Graph(HashMap<Literal, Boolean> satisfiability){
		this.satisfiability = satisfiability;
	}

	
	//Depth-First Search recursive.
	//Counter is used during SCC DFS to separate SCC into several index in the array list
	public void DFS_visit(Graph graph, int counter, Literal s, boolean isSCC) {
		if (isSCC) { //Check if we are finding SCC
			HashMap<Literal, Boolean> innerSCC = SCC.get(counter); //get the hashmap for the SCC
			innerSCC.put(s, null); //insert literal to the hashmap
//			System.out.println(s);
//			System.out.println(innerSCC);
//			System.out.println(SCC);
		}
		ArrayList<Literal> neighbours = graph.adj.get(s); //Get the array list containing neighbours
		if (neighbours == null){ //If there are no neighbours, end.
			if (!S.contains(s) && !isSCC) {
				S.push(s);
			}
			return;
		}
		for(Literal v : neighbours) {
			if(graph.parent.get(v) == null) { //If the literal is already traversed, do nothing.
				graph.parent.put(v, s);
				DFS_visit(graph, counter, v, isSCC);
			}
		}
		//Generate stack based on DFS finish time
		if (!S.contains(s) && !isSCC) {
			S.push(s);
		}
	}

	//Depth-First Search implementation.
	//isSCC checks if this is normal DFS or DFS to find SCC
	public void DFS(Graph graph, boolean isSCC) {
		for(Literal s : this.satisfiability.keySet()) {
			if(parent.get(s) == null) {
				parent.put(s, s);
				DFS_visit(graph,0, s, isSCC);
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
		HashMap<Literal, ArrayList<Literal>> adjTranspose = transposedGraph.getAdj(); //get the adjacency hashmap of the transposed graph
		for (Literal lit1 : this.satisfiability.keySet()){ //Traversing all vertices
			ArrayList<Literal> neighbours = this.adj.get(lit1); //get List containing literals adjacent to lit1
			if (neighbours != null) {
				for (Literal lit2 : neighbours) { //iterate through the list of adjacent literals
					// get the list storing the adjacent literals of lit2
					ArrayList<Literal> lit2adj = adjTranspose.get(lit2);
					if (lit2adj == null) { //If it doesn't exist, initialise
						lit2adj = new ArrayList<>();
					}
					lit2adj.add(lit1);
					adjTranspose.put(lit2, lit2adj);
				}
			}
			else {
				//do nothing
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
		//Counter represent the index of the current SCC that the DFS is in.
		int counter = 0;
		//Traverse through the vertex in topological order of graph G. Done by popping from DFS finish-time stack
		while (!S.empty()){
			Literal v = S.pop();
			if (!transposedGraph.parent.containsKey(v)) {
				transposedGraph.parent.put(v, v);
				SCC.add(new HashMap<Literal, Boolean>()); //Allocate space for next SCC
				DFS_visit(transposedGraph, counter, v, true);
				counter++; //If DFS for a vertex is done, increase counter to move on to the next SCC
			}
		}
	}
	
	//Reverse topological order --> From counter high to low
	public void solve(){
		generateSCC();
		for (int i = SCC.size() - 1; i >= 0 ; i--) {
			HashMap<Literal, Boolean> innerSCC = SCC.get(i);
			for (Literal lit : innerSCC.keySet()) {
				//Check if the Literal is already marked
				if (satisfiability.get(lit) == null) {
					//Check for contradiction
					if (innerSCC.containsKey(lit.getNegation())) {
						satisfiable = false;
						return;
					} else {
						//Mark Literal as true and !Literal as false
						satisfiability.put(lit, true);
						satisfiability.put(lit.getNegation(), false);
					}
				}
			}
		}
		//If no contradiction occurs, it is satisfiable
		satisfiable = true;
	}
	
	public HashMap<Literal, ArrayList<Literal>> getAdj(){
		return this.adj;
	}

	public void display() {
		//display the graph
		for(Literal lit : adj.keySet()) {
			System.out.print(lit + ": ");

			for(Literal v : adj.get(lit)) {
				System.out.print(v + ", ");
			}
			System.out.println();
		}
		//display the satisfiability assignment if it is satisfiable
		if (satisfiable) {
			for (Literal lit : satisfiability.keySet()) {
				System.out.println("" + lit + satisfiability.get(lit));
			}
			System.out.println("Satisfiable");
		} else {
			System.out.println("Not Satisfiable");
		}

	}
}

