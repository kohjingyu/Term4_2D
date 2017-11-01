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

public class Graph {
	public HashMap<Literal, ArrayList<Literal>> adj = new HashMap<>(); // Adjacency list
	public HashMap<Literal, Literal> parent = new HashMap<>();
	private HashMap<Literal, Boolean> satisfiability = new HashMap<>();
	private ArrayList<HashMap<Literal, Boolean>> SCC = new ArrayList<>(); // All vertices in the graph
	private Stack<Literal> S = new Stack<>();
	private boolean satisfiable;

	public Graph(Formula formula) {
		for(Clause c : formula.getClauses()) {
			if(c.size() > 2) {
				System.out.println("Not a 2SAT problem!");
				break;
			}
			else if(c.size() == 0) {
				// Trivial case: false
				// TODO: Return false
				satisfiable = false;
			}
			else if(c.size() == 1) {
				Literal lit = c.chooseLiteral();
				Literal nLit = lit.getNegation();
				// Add vertex
				satisfiability.put(lit,null);
				satisfiability.put(nLit,null);
//				V.add(lit);
//				V.add(nLit);
			}
			else {
				Iterator<Literal> iterator = c.iterator();

				Literal firstLit = iterator.next();
				Literal nFirstLit = firstLit.getNegation();
				Literal secondLit = iterator.next();
				Literal nSecondLit = secondLit.getNegation();

				// Add literals to vertex array
				satisfiability.put(firstLit, null);
				satisfiability.put(nFirstLit, null);
				satisfiability.put(secondLit, null);
				satisfiability.put(nSecondLit, null);
				

				// For a clause (a OR b)
				// Add edges ~a -> b and ~b -> a for each clause
				ArrayList<Literal> firstLitAdj = adj.get(nFirstLit);
				ArrayList<Literal> secondLitAdj = adj.get(nSecondLit);

				// If the vertex has edges already, append. If it doesn't, initiate the ArrayList
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
	
	public Graph(HashMap<Literal, Boolean> satisfiability){
//		this.V = V;
		this.satisfiability = satisfiability;
	}

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
			return;
		}
		for(Literal v : neighbours) {
			if(graph.parent.get(v) == null) { //If the literal is already traversed, do nothing.
				graph.parent.put(v, s);
				DFS_visit(graph, counter, v, isSCC);
			}
		}
		if (!S.contains(s) && !isSCC) {
			S.push(s);
		}
	}
	
//	public void DFS_visitSCC(Literal s) {
//		SCC.add(s);
//		ArrayList<Literal> adjVertices = this.adj.get(s);
//		for(Literal v : adjVertices) {
//			if(this.parent.get(v) == null) {
//				this.parent.put(v, s);
//				DFS_visitSCC(v);
//
//			}
//		}
		
//	}

	public void DFS(Graph graph, boolean isSCC) {
		for(Literal s : this.satisfiability.keySet()) {
			if(parent.get(s) == null) {
				parent.put(s, s);
				DFS_visit(graph,0, s, isSCC);
			}
			if (!S.contains(s) && !isSCC) {
				S.push(s);
			}
		}
		
	}
	
	public ArrayList<HashMap<Literal, Boolean>> getSCC(){ //Create Strongly Connected Component
		this.DFS(this, false);
		Graph transposedGraph = this.getTranspose();
		//Clear SCC and Parent for second DFS
		SCC.clear();
		parent.clear();
		int counter = 0;
		System.out.println(S);
		while (!S.empty()){
			Literal v = S.pop();
			if (!transposedGraph.parent.containsKey(v)) {
				transposedGraph.parent.put(v, v);
				SCC.add(new HashMap<Literal, Boolean>()); //Allocate space
				DFS_visit(transposedGraph, counter, v, true);
				counter++;
			}
		}
		System.out.println("I'm here");
		return SCC;
		
	}
	
	//Reverse topological order --> From counter high to low
	public void solve(){
		getSCC();
		for (int i = SCC.size() - 1; i >= 0 ; i--) {
			HashMap<Literal, Boolean> innerSCC = SCC.get(i);
//			System.out.println(innerSCC);
			for (Literal lit : innerSCC.keySet()) {
				if (satisfiability.get(lit) == null) { //check if the boolean value is already assigned to the literal
					if (innerSCC.containsKey(lit.getNegation())) { //Check for contradiction
						System.out.println(false);
						return;
					} else {
						satisfiability.put(lit, true);
						satisfiability.put(lit.getNegation(), false);
					}
				}
			}
		}
		System.out.println(SCC);
		System.out.println(true);
//		for (Literal lit : satisfiability.keySet()){
//			System.out.println("" + lit + satisfiability.get(lit));
//		}
	}
	

	
	public Graph getTranspose(){
		Graph newGraph = new Graph(this.satisfiability);
		HashMap<Literal, ArrayList<Literal>> adjTranspose = newGraph.getAdj();
		for (Literal lit1 : this.satisfiability.keySet()){
			ArrayList<Literal> neighbours = this.adj.get(lit1); //get the literals adjacent to lit1
			if (neighbours != null) {
				for (Literal lit2 : neighbours) { //iterate through the adjacent literals
					 // get the list storing the adjacent literals of lit2
					ArrayList<Literal> lit2adj = adjTranspose.get(lit2);
					if (lit2adj == null) { //If it doesn't exist, initialise
						lit2adj = new ArrayList<>();
						lit2adj.add(lit1);
						adjTranspose.put(lit2, lit2adj);
					} else {
						lit2adj.add(lit1);
					}
				}
			}
		}
//		newGraph.display();
		return newGraph;
		
	}
	
	public HashMap<Literal, ArrayList<Literal>> getAdj(){
		return this.adj;
	}

	public void display() {
		for(Literal lit : adj.keySet()) {
			System.out.print(lit + ": ");

			for(Literal v : adj.get(lit)) {
				System.out.print(v + ", ");
			}
			System.out.println();
		}
//		for (Literal lit : satisfiability.keySet()){
//			System.out.println("" + lit + satisfiability.get(lit));
//		}

	}
}

