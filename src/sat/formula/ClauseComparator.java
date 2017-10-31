package sat.formula;

import java.util.Comparator;

/**
 * Created by Angelia on 31/10/17.
 */

public class ClauseComparator implements Comparator<Clause> {

    public int compare(Clause a, Clause b){
        if (a.size()>b.size()) return 1;
        else if (a.size()<b.size()) return -1;
        else return 0;
    }


}
