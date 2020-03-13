import java.util.Arrays;


class SparseDom {
    int pointer = -1;
    int[] dom = null;
    private int[] idx = null;
    public SparseDom(int D) {
        pointer = D - 1;
        dom = new int[D];
        idx = new int[D];
        for (int i = 0; i< D; i++) {
            dom[i] = i;
            idx[i] = i;
        }
    }
    void delete(int index) {
        int val = dom[index];
        int tail_val = dom[pointer];
        dom[index] = tail_val;
        idx[tail_val] = index;
        dom[pointer] = val;
        idx[val] = pointer;
        pointer -= 1;
    }
    void assign(int val) {
        int idx_v = idx[val];
        int head_val = dom[0];
        dom[0] = val;
        idx[val] = 0;
        dom[idx_v] = head_val;
        idx[head_val] = idx_v;
        pointer = 0;
    }
}

class BackTrackSearcher {
    private int[][][][] cons_map;
    private SparseDom[] vars_map;
    private int N = 0;
    private int D = 0;
    int count = 0;
    private SparseDom[] answer = null;

    private int heapSize = 0;
    private int[] heapList;
    private int[] heapMap;

    private long[] ts_v;
    private long[][] ts_c;
    private long ts_global = 2;

    private boolean[] assign_map;

    BackTrackSearcher(int[][][][] rel_, SparseDom[] vars_, int N, int D) {
        cons_map = rel_;
        vars_map = vars_;
        this.N = N;
        this.D = D;

        heapList = new int[N];
        heapMap = new int[N];

        ts_v = new long[N];
        ts_c = new long[N][];

        assign_map = new boolean[N];

        for (int i = 0; i < N; i++) {
            heapList[i] = -1;
            heapMap[i] = -1;
            ts_v[i] = 1;
            ts_c[i] = new long[N];
            for (int j = 0; j < N; j++) {
                ts_c[i][j] = 0;
            }
            assign_map[i] = false;
        }
    }

    private void push(int x) {
        int pos = heapSize;
        int qos = pos;

        heapSize += 1;

        while (pos != 0) {
            pos = (pos - 1) / 2;
            int a = heapList[pos];
            if (vars_map[a].pointer < vars_map[x].pointer) {
                break;
            }
            heapList[qos] = a;
            heapMap[a] = qos;
            qos = pos;
        }
        heapList[qos] = x;
        heapMap[x] = qos;
    }

    private int pop() {
        int a = heapList[0];
        heapSize -= 1;
        heapList[0] = heapList[heapSize];
        heapMap[heapList[heapSize]] = 0;
        heap_down(0);
        heapMap[a] = -1;
        return a;
    }

    private void heap_down(int pos) {
        int x = heapList[pos];
        int qos = pos * 2 + 1;
        while (qos < heapSize - 1) {
            int b = heapList[qos + 1];
            int a = heapList[qos];
            if (vars_map[b].pointer < vars_map[a].pointer) {
                qos += 1;
                a = b;
            }
            if (vars_map[a].pointer > vars_map[x].pointer) {
                heapList[pos] = x;
                heapMap[x] = pos;
                break;
            }
            heapList[pos] = a;
            heapMap[a] = pos;
            pos = qos;
            qos = pos * 2 + 1;
        }
        if (qos > heapSize - 1) {
            heapList[pos] = x;
            heapMap[x] = pos;
        }
        else if (qos == heapSize - 1) {
            int a = heapList[qos];
            if (vars_map[a].pointer > vars_map[x].pointer) {
                heapList[pos] = x;
                heapMap[x] = pos;
            }
            else {
                heapList[pos] = a;
                heapMap[a] = pos;
                heapList[qos] = x;
                heapMap[x] = qos;
            }
        }
    }

    private void heap_up(int x) {
        int pos = heapMap[x];
        int qos = pos;
        while (pos > 0) {
            pos = (pos - 1) / 2;
            int a = heapList[pos];
            if (vars_map[a].pointer < vars_map[x].pointer) {
                break;
            }
            heapList[qos] = a;
            heapMap[a] = qos;
            qos = pos;
        }
        heapList[qos] = x;
        heapMap[x] = qos;
    }

    private void heap_clear() {
        for (int i = 0; i < heapSize; i++) {
            int x = heapList[i];
            heapMap[x] = -1;
        }
        heapSize = 0;
    }

    private int var_heuristics() {
        int min_dom = 10000;
        int min_index = -1;
        for (int i = 0; i < N; i++) {
            if (vars_map[i].pointer > 0) {
                if (vars_map[i].pointer <= min_dom) {
                    min_index = i;
                    min_dom = vars_map[i].pointer;
                }
            }
        }
        return min_index;
    }

    private boolean revise(int x, int y) {
        int[][] con_map = cons_map[x][y];
        int x_pre = vars_map[x].pointer;
        for (int i = vars_map[x].pointer; i >= 0; i--) {
            int val_x = vars_map[x].dom[i];
            boolean find_sup = false;
            for (int j = 0; j <= vars_map[y].pointer; j++) {
                int val_y = vars_map[y].dom[j];
                if (con_map[val_x][val_y] == 1) {
                    find_sup = true;
                    break;
                }
            }
            if (!find_sup) {
                vars_map[x].delete(i);
            }
        }
        if (vars_map[x].pointer != x_pre) {
            if (vars_map[x].pointer < 0) {
                return true;
            }
            ts_v[x] = ts_global;
            ts_global += 1;
            if (heapMap[x] == -1) {
                push(x);
            }
            else {
                heap_up(x);
            }
        }
        return false;
    }

    private boolean ac_enforcer(int var_id) {
        if (var_id == -1) {
            for (int i = 0; i < N; i++) {
                push(i);
            }
        }
        else {
            push(var_id);
        }

        while (heapSize > 0) {
            int var = pop();
            for (int i = 0; i < N; i++) {
                if (var != i && ts_v[var] > ts_c[var][i]) {
                    if (revise(var, i) || (!assign_map[i] && revise(i, var))) {
                        heap_clear();
                        return false;
                    }
                    ts_c[var][i] = ts_global;
                    ts_c[i][var] = ts_global;
                    ts_global += 1;
                }
            }
        }
        return true;
    }

    boolean dfs(int level, int var_index) {
        count += 1;
        System.out.println(level + " " + count);
        if (level == N) {
            answer = vars_map;
            return true;
        }
        if (!ac_enforcer(var_index)) {
            return false;
        }
        var_index = var_heuristics();
        if (var_index == -1) {
            answer = vars_map;
            return true;
        }

        int[] back_vars = new int[N];
        for (int i = 0; i < N; i++) {
            back_vars[i] = vars_map[i].pointer;
        }
        int[] sorted_dom = new int[vars_map[var_index].pointer + 1];
        for (int i = 0; i <= vars_map[var_index].pointer; i++) {
            sorted_dom[i] = vars_map[var_index].dom[i];
        }
        Arrays.sort(sorted_dom);
        assign_map[var_index] = true;
        for (int ii = 0; ii <= vars_map[var_index].pointer; ii++) {
            int i = sorted_dom[ii];
            vars_map[var_index].assign(i);
            ts_v[var_index] = ts_global;
            ts_global += 1;
            if (dfs(level + 1, var_index)) {
                return true;
            }
            for (int j = 0; j < N; j++) {
                vars_map[j].pointer = back_vars[j];
                ts_v[j] = 0;
            }
        }
        assign_map[var_index] = false;
        return false;
    }
}

public class CpuMain {
    public static void main(String[] args) {
        int[][][][] constraints_map = ConstraintGenerator.generator(20, 100, 10, false);
        int max_domain = constraints_map.length;
        int num_variables = constraints_map[1].length;

        SparseDom[] variables_map = new SparseDom[num_variables];
        for (int i = 0; i < num_variables; i++) {
            variables_map[i] = new SparseDom(max_domain);
        }

        BackTrackSearcher bs = new BackTrackSearcher(constraints_map, variables_map, num_variables, max_domain);

        boolean satisfied = bs.dfs(0, -1);
        System.out.println(bs.count);
        System.out.println(satisfied);
    }

}