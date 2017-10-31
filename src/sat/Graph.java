package sat;

import immutable.ImList;
import immutable.ImMap;

import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Stack;

public class Graph {
	private HashMap<Literal, ArrayList<Literal>> adj = new HashMap<>(); // Adjacency list
	private HashMap<Literal, Literal> parent = new HashMap<>();
	private ArrayList<Literal> V, SCC = new ArrayList<>(); // All vertices in the graph
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
				V.add(lit);
				V.add(nLit);
			}
			else {
				Iterator<Literal> iterator = c.iterator();

				Literal firstLit = iterator.next();
				Literal nFirstLit = firstLit.getNegation();
				Literal secondLit = iterator.next();
				Literal nSecondLit = secondLit.getNegation();

				// Add literals to vertex array
				V.add(firstLit);
				V.add(nFirstLit);
				V.add(secondLit);
				V.add(nSecondLit);

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
	
	public Graph(ArrayList<Literal> V){
		this.V = V;
	}

	public void DFS_visit(Graph graph, int counter, Literal s) {
		SCC.add(counter, s);
		ArrayList<Literal> adjVertices = this.adj.get(s);
		for(Literal v : adjVertices) {
			if(this.parent.get(v) == null) {
				this.parent.put(v, s);
				DFS_visit(graph, counter, v);
			}
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

	public void DFS(Graph graph) {
		for(Literal s : this.V) {
			if(parent.get(s) == null) {
				parent.put(s, null);
				DFS_visit(graph,0, s);
			}
			S.push(s);
		}
		
	}
	
	public ArrayList<Literal> getSCC(){ //Create Strongly Connected Component
		this.DFS(this);
		Graph transposedGraph = this.getTranspose();
		HashMap<Literal, ArrayList<Literal>> scc = new HashMap<>();
		//Clear SCC and Parent for second DFS
		SCC.clear();
		parent.clear();
		int counter = 0;
		while (!S.empty()){
			Literal v = S.pop();
			DFS_visit(transposedGraph, counter, v);
			counter++;
		}
		return SCC;
		
	}
	
	public Graph getTranspose(){
		Graph newGraph = new Graph(this.V);
		for (Literal lit1 : this.V){
			ArrayList<Literal> adjacency = this.adj.get(lit1);
			for (Literal lit2 : adjacency){
				ArrayList<Literal> lit2adj = newGraph.adj.get(lit2);
				if ( lit2adj == null) {
					lit2adj = new ArrayList<Literal>();
					lit2adj.add(lit2);
				}
				else {
					lit2adj.add(lit2);
				}
			}
		}
		return newGraph;
	}

	public void display() {
		for(Literal lit : adj.keySet()) {
			System.out.print(lit + ": ");

			for(Literal v : adj.get(lit)) {
				System.out.print(v + ", ");
			}

			System.out.println();
		}
	}
}

