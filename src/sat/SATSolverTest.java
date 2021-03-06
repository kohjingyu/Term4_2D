package sat;

import static org.junit.Assert.*;

import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;

import org.junit.Test;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import sat.env.*;
import sat.formula.*;

import sat.env.Variable;
import immutable.ImListMap;
import immutable.ImMap;

public class SATSolverTest {
    Literal a = PosLiteral.make("a");
    Literal b = PosLiteral.make("b");
    Literal c = PosLiteral.make("c");
    Literal na = a.getNegation();
    Literal nb = b.getNegation();
    Literal nc = c.getNegation();

    public static void main(String[] args) {
        // Read the .cnf file and calls SATSolver.solve to determine the satisfiability
        if(args.length == 0) {
            System.out.println("Error: please provide a cnf file.");
        }
        else {
            try {
                Path path = Paths.get(args[0]);
                BufferedReader reader = Files.newBufferedReader(path, StandardCharsets.UTF_8);

                // Find p line
                Clause[] clauses = null;
                ArrayList<Literal> currentLiterals = new ArrayList<Literal>();
                int numVariables = 0;
                int degree = 0;
                int numClauses = 0;
                int currentClause = 0;

                String line = null;
                while ((line = reader.readLine()) != null) {
                    line = line.replace("\n", ""); // Remove newline
                    String[] splitted = line.split("\\s+"); // Split by whitespace

                    // Make sure it is not an empty line
                    if(splitted.length > 0 && !line.equals("")) {
                        if(splitted[0].equals("p")) {
                            // Get variable names
                            if(splitted.length == 4 || !splitted[1].equals("cnf"))
                            {
                                numVariables = Integer.valueOf(splitted[2]);
                                numClauses = Integer.valueOf(splitted[3]);
                                clauses = new Clause[numClauses]; // Create an array of size 'numClauses'
                                
                            }
                            else {
                                throw new IOException("INVALID INPUT");
                            }
                        }
                        else if(!splitted[0].equals("c")) {
                            // Not format, not comment, this is a clause
                            for(String numStr : splitted) {
                                int intValue = Integer.valueOf(numStr);

                                if(intValue == 0) {
                                    // End of clause, add to clauses
                                    Literal[] clauseLiterals = currentLiterals.toArray(new Literal[currentLiterals.size()]);
                                    Clause newCl = makeCl(clauseLiterals);

                                    if(clauseLiterals.length > degree) {
                                        degree = clauseLiterals.length;
                                    }
                                    clauses[currentClause] = newCl;
                                    currentLiterals.clear();
                                    currentClause += 1;
                                }
                                else {
                                    // Add literal to current literals
                                    if(intValue < 0) {
                                        // Negative literal
                                        int positiveValue = intValue * -1;
                                        Literal posLit = PosLiteral.make(String.valueOf(positiveValue));
                                        Literal lit = posLit.getNegation();
                                        currentLiterals.add(lit);
                                    }
                                    else {
                                        // Positive literal
                                        Literal lit = PosLiteral.make(String.valueOf(intValue));
                                        currentLiterals.add(lit);
                                    }
                                }
                            }
                        }
                    }
                }

                // Final formula
                System.out.println("SAT solver starts!!!");
                long started = System.nanoTime();

                Formula fm = makeFm(clauses);
                SATSolver solver = new SATSolver();
                HashMap<Variable,Bool> results = solver.solve(fm, degree);
                if (results == null) System.out.println("not satisfiable");
                else System.out.println("satisfiable");

                long time = System.nanoTime();
                long timeTaken= time - started;
                System.out.println("Time:" + timeTaken/1000000.0 + "ms");

                System.out.println("Printing out the results into file...");
                PrintWriter writer = new PrintWriter(args[1]);
                if(results == null){
                    writer.println(results);
                }else{
                    Iterator it = results.entrySet().iterator();
                    while(it.hasNext()){
                        Map.Entry pair = (Map.Entry)it.next();
                        writer.println(pair.getKey()+":"+pair.getValue());
                        it.remove();
                    }
                }
                writer.close();
                System.out.println("Printing complete.");
                
//                long time = System.nanoTime();
//                long timeTaken= time - started;
//                System.out.println("Time:" + timeTaken/1000000.0 + "ms");

            }
            catch(IOException e){
                System.out.println(e);
            }
        }
    }

	
	
    public void testSATSolver1(){
    	// (a v b)
    	HashMap<Variable, Bool> e = SATSolver.solve(makeFm(makeCl(a,b))	);

    	assertTrue( "one of the literals should be set to true",
    			Bool.TRUE == e.get(a.getVariable())
    			|| Bool.TRUE == e.get(b.getVariable())	);
    	
    }
    
    
    public void testSATSolver2(){
    	// (~a)
    	HashMap<Variable, Bool> e = SATSolver.solve(makeFm(makeCl(na)));
    	assertEquals( Bool.FALSE, e.get(na.getVariable()));
    }
    
    private static Formula makeFm(Clause... e) {
        Formula f = new Formula();
        for (Clause c : e) {
            if(c != null) {
                f = f.addClause(c);
            }
        }
        return f;
    }
    
    private static Clause makeCl(Literal... e) {
        Clause c = new Clause();
        for (Literal l : e) {
            c = c.add(l);
        }
        return c;
    }
    
    
    
}