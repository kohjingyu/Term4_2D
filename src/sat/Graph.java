package sat;

import immutable.ImList;
import immutable.ImMap;

import sat.formula.Clause;
import sat.formula.Formula;
import sat.formula.Literal;

import java.util.ArrayList;
import java.util.HashMap;

public class Graph {
	private HashMap<Literal, ArrayList<Literal>> adj = new HashMap<Literal, ArrayList<Literal>>();
	private ArrayList<Literal> V = new ArrayList<Literal>();

	public Graph(Formula formula) {
		for(Clause c : formula.getClauses()) {
			if(c.size() > 2) {
				System.out.println("Not a 2SAT problem!");
				break;
			}

			for(Literal lit : c) {
				
			}
		}
	}

	public void DFS_visit(HashMap<Literal, Literal> parent, Literal s) {
		ArrayList<Literal> adjVertices = this.adj.get(s);
		for(Literal v : adjVertices) {
			if(parent.get(v) == null) {
				parent.put(v, s);
				DFS_visit(parent, v);
			}
		}
	}

	public void DFS() {
		HashMap<Literal, Literal> parent = new HashMap<Literal, Literal>();
		for(Literal s : this.V) {
			if(parent.get(s) == null) {
				parent.put(s, null);
				DFS_visit(parent, s);
			}
		}
	}
}

