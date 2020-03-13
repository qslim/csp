public class ConstraintGenerator {
    static int[][][][] generator(int max_dom, int num_vars, int density, boolean diffy) {
        int num_cons = num_vars;
        if (diffy) {
            num_cons = num_vars * (num_vars - 1) / 2;
        }
        int[][][] rels_map = new int[num_cons][][];
        int[][][] rels_map_r = new int[num_cons][][];
        for (int r1 = 0; r1 < num_cons; r1++) {
            int[][] rel_map = new int[num_cons][num_cons];
            int[][] rel_map_r = new int[num_cons][num_cons];
            for (int i1 = 0; i1 < max_dom; i1++) {
                for (int i2 = 0; i2 < max_dom; i2++) {
                    int val = (int)(Math.random()*10);
                    if (val > 0) {
                        rel_map[i1][i2] = 1;
                        rel_map_r[i2][i1] = 1;
                    }
                }
            }
            rels_map[r1] = rel_map;
            rels_map_r[r1] = rel_map_r;
        }

        int[][] cons_mark = new int[num_vars][num_vars];
        for (int i = 0; i < num_vars; i++) {
            for (int j = 0; j < num_vars; j++) {
                cons_mark[i][j] = -1;
            }
        }
        int cnt = 0;
        for (int i=0; i < num_vars; i++) {
            for (int j = 0; j < num_vars; j++) {
                if (i == j) {
                    continue;
                }
                if (i < j) {
                    cons_mark[i][j] = cnt % num_cons;
                    cons_mark[j][i] = cnt % num_cons;
                    cnt += 1;
                }
            }
        }

        int[][] eye = new int[num_vars][num_vars];
        for (int i = 0; i < num_vars; i++) {
            eye[i][i] = 1;
        }
        int[][][][] cons_map = new int[num_vars][num_vars][][];
        for (int i = 0; i < num_vars; i++) {
            int[][][] cube = new int[num_vars][][];
            for (int j = 0; j < num_vars; j++) {
                if (i == j) {
                    cube[j] = eye;
                }
                else if (i < j) {
                    cube[j] = rels_map[cons_mark[i][j]];
                }
                else {
                    cube[j] = rels_map_r[cons_mark[j][i]];
                }
            }
            cons_map[i] = cube;
        }
        return cons_map;
    }

    public static void main(String[] args) {
        int[][][][] tmp = ConstraintGenerator.generator(3, 3, 10, true);
        System.out.println(tmp.length);
    }
}
