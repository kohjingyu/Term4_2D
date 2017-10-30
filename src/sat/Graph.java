package sat;

import immutable.ImList;
import immutable.ImMap;

import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;

public class Graph {
	private HashMap<Literal, ArrayList<Literal>> adj = new HashMap<Literal, ArrayList<Literal>>(); // Adjacency list
	private HashMap<Literal, Literal> parent = new HashMap<Literal,Literal>();
	private ArrayList<Literal> V = new ArrayList<Literal>(); // All vertices in the graph

	public Graph(Formula formula) {
		for(Clause c : formula.getClauses()) {
			if(c.size() > 2) {
				System.out.println("Not a 2SAT problem!");
				break;
			}
			else if(c.size() == 0) {
				// Trivial case: false
				// TODO: Return false
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

				// If the vertex has edges already, append. If it doens't, initiate the ArrayList
				if(firstLitAdj == null) {
					firstLitAdj = new ArrayList<Literal>();
				}
				firstLitAdj.add(secondLit);

				if(secondLitAdj == null) {
					secondLitAdj = new ArrayList<Literal>();
				}
				secondLitAdj.add(firstLit);

				adj.put(nFirstLit, firstLitAdj);
				adj.put(nSecondLit, secondLitAdj);
			}
		}
	}

	public void DFS_visit(Literal s) {
		ArrayList<Literal> adjVertices = this.adj.get(s);
		for(Literal v : adjVertices) {
			if(this.parent.get(v) == null) {
				this.parent.put(v, s);
				DFS_visit(v);
			}
		}
	}

	public void DFS() {
		for(Literal s : this.V) {
			if(parent.get(s) == null) {
				parent.put(s, null);
				DFS_visit(s);
			}
		}
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

