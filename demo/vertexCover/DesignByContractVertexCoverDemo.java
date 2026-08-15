/**
 * 
 */
package vertexCover;


/**
 * @author Yannis Tzitzikas (yannistzitzik@gmail.com)
 *
 * Analogous to DesignByContractComplexityDemo (Partition) and
 * DesignByContractSatDemo, but for the Minimum Vertex Cover problem.
 *
 * Practical exploitation of the Uncertainty-Parametric complexity framework
 * (UP[K]) using Design-by-Contract (DbC).
 *
 * Theory Connection:
 *  - C_verify(K)   : Linear guard check O(V+E) verifying the structural
 *                    property K (bipartiteness via 2-coloring; connectedness
 *                    via BFS).
 *  - P_u[K] Solver :
 *       K_TRIVIAL   : no edges                  -> O(1).
 *       K_TREE      : roots + linear DP over the tree -> O(V).
 *       K_BIPARTITE : Konig's theorem: min vertex cover = max matching,
 *                     computed by Hopcroft-Karp     -> O(E*sqrt(V)).
 *  - SLA Safety     : unstructured (K = epsilon) large non-bipartite graphs
 *                     are rejected before worst-case exponential search.
 *
 * Java 8 compatible.
 */

import java.util.ArrayDeque;
import java.util.Arrays;

public class DesignByContractVertexCoverDemo {

    // --- Contract & SLA Infrastructure -----------------------------------

    public static class ExecutionReport {
        private final int numVertices;
        private final int numEdges;
        private final int coverSize;          // minimum vertex cover size
        private final String matchedPropertyK;
        private final long verificationTimeNanos;
        private final long executionTimeNanos;
        private final long totalTimeNanos;
        private final boolean slaGuaranteed;

        public ExecutionReport(int numVertices, int numEdges, int coverSize,
                               String matchedPropertyK, long verificationTimeNanos,
                               long executionTimeNanos, long totalTimeNanos,
                               boolean slaGuaranteed) {
            this.numVertices = numVertices;
            this.numEdges = numEdges;
            this.coverSize = coverSize;
            this.matchedPropertyK = matchedPropertyK;
            this.verificationTimeNanos = verificationTimeNanos;
            this.executionTimeNanos = executionTimeNanos;
            this.totalTimeNanos = totalTimeNanos;
            this.slaGuaranteed = slaGuaranteed;
        }

        public int getNumVertices()          { return numVertices; }
        public int getNumEdges()             { return numEdges; }
        public int getCoverSize()            { return coverSize; }
        public String getMatchedPropertyK()  { return matchedPropertyK; }
        public long getVerificationTimeNanos() { return verificationTimeNanos; }
        public long getExecutionTimeNanos()  { return executionTimeNanos; }
        public long getTotalTimeNanos()      { return totalTimeNanos; }
        public boolean isSlaGuaranteed()     { return slaGuaranteed; }
    }

    public static class SlaBreachException extends RuntimeException {
        public SlaBreachException(String message) { super(message); }
    }

    // --- Uncertainty-Aware Vertex Cover Solver ---------------------------

    public static class ParametricVertexCoverSolver {

        // Strict Microservice SLA threshold: 5.0 milliseconds
        private static final long SLA_THRESHOLD_NANOS = 5_000_000L;
        // Brute force is only allowed for tiny graphs (2^V subsets).
        private static final int BRUTE_FORCE_MAX_V = 20;

        /**
         * Solves Minimum Vertex Cover under Design-by-Contract.
         *
         * The graph is given as adjacency lists: adj[u] = neighbours of u,
         * vertices are 0..V-1, and the graph is undirected.
         *
         * First performs a single O(V+E) guard scan C_verify(K) to determine the
         * structural property K (tree / bipartite / unstructured). If K holds, it
         * dispatches to a fast solver; otherwise it falls back to (or rejects)
         * unstructured input.
         */
        public ExecutionReport solveSlaGuaranteed(int[][] adj) {
            long startNanos = System.nanoTime();

            int V = adj.length;
            if (V == 0) {
                return new ExecutionReport(0, 0, 0, "K_EMPTY", 0, 0, 0, true);
            }

            // =========================================================================
            // TIER 1: Guard Predicates C_verify(K) - single O(V+E) scan
            // =========================================================================
            int m = 0;
            for (int u = 0; u < V; u++) m += adj[u].length;
            m /= 2; // undirected: each edge counted twice

            // 2-coloring of the full graph (all connected components) + connectedness.
            int[] color = new int[V];
            Arrays.fill(color, -1);
            boolean bipartite = true;
            ArrayDeque<Integer> queue = new ArrayDeque<>();

            for (int src = 0; src < V; src++) {
                if (color[src] != -1) continue;
                color[src] = 0;
                queue.add(src);
                while (!queue.isEmpty()) {
                    int u = queue.poll();
                    for (int w : adj[u]) {
                        if (color[w] == -1) {
                            color[w] = 1 - color[u];
                            queue.add(w);
                        } else if (color[w] == color[u]) {
                            bipartite = false; // odd cycle
                        }
                    }
                }
            }

            // Connectedness: is vertex 0 able to reach every vertex?
            boolean connected;
            {
                boolean[] seen = new boolean[V];
                ArrayDeque<Integer> q = new ArrayDeque<>();
                seen[0] = true;
                q.add(0);
                int cnt = 1;
                while (!q.isEmpty()) {
                    int u = q.poll();
                    for (int w : adj[u]) {
                        if (!seen[w]) { seen[w] = true; q.add(w); cnt++; }
                    }
                }
                connected = (cnt == V);
            }
            boolean isTree = connected && (m == V - 1);

            long verifyTimeNanos = System.nanoTime() - startNanos;

            // =========================================================================
            // TIER 2: P_u[K] Dispatching - structural collapse
            // =========================================================================

            // K_TRIVIAL: no edges -> empty cover.
            if (m == 0) {
                long execTimeNanos = 0L;
                long totalNanos = System.nanoTime() - startNanos;
                return new ExecutionReport(V, m, 0, "K_TRIVIAL (no edges)",
                        verifyTimeNanos, execTimeNanos, totalNanos,
                        totalNanos <= SLA_THRESHOLD_NANOS);
            }

            // K_TREE: connected acyclic graph -> linear-time tree DP.
            if (isTree) {
                long eStart = System.nanoTime();
                int cs = minVertexCoverTree(adj, V);
                long execTimeNanos = System.nanoTime() - eStart;
                long totalNanos = System.nanoTime() - startNanos;
                return new ExecutionReport(V, m, cs, "K_TREE (linear DP)",
                        verifyTimeNanos, execTimeNanos, totalNanos,
                        totalNanos <= SLA_THRESHOLD_NANOS);
            }

            // K_BIPARTITE: polynomial via Konig's theorem (max matching).
            if (bipartite) {
                long eStart = System.nanoTime();
                int cs = minVertexCoverBipartite(adj, V, color);
                long execTimeNanos = System.nanoTime() - eStart;
                long totalNanos = System.nanoTime() - startNanos;
                return new ExecutionReport(V, m, cs, "K_BIPARTITE (Konig)",
                        verifyTimeNanos, execTimeNanos, totalNanos,
                        totalNanos <= SLA_THRESHOLD_NANOS);
            }

            // =========================================================================
            // TIER 3: Fallback / Unstructured (K = epsilon) Safety Protection
            // =========================================================================

            // Non-bipartite graphs with no structure cannot satisfy deterministic
            // SLA bounds for large V. Reject by Contract.
            if (V > BRUTE_FORCE_MAX_V) {
                throw new SlaBreachException(
                    "Design-by-Contract Violation: Non-bipartite graph with V=" + V +
                    " lacks structural property K (K=\\epsilon) and exceeds " +
                    "deterministic SLA execution bounds.");
            }

            // Small fallback: exhaustive search over all 2^V subsets.
            long eStart = System.nanoTime();
            int cs = minVertexCoverBruteForce(adj, V);
            long execTimeNanos = System.nanoTime() - eStart;
            long totalNanos = System.nanoTime() - startNanos;
            return new ExecutionReport(V, m, cs, "K_UNSTRUCTURED (brute force)",
                    verifyTimeNanos, execTimeNanos, totalNanos,
                    totalNanos <= SLA_THRESHOLD_NANOS);
        }

        // -------------------------------------------------------------------
        // K_TREE: minimum vertex cover on a tree, linear iterative DP O(V)
        // -------------------------------------------------------------------
        private int minVertexCoverTree(int[][] adj, int n) {
            if (n == 0) return 0;

            // Root at vertex 0; compute parent + preorder via an explicit stack
            // (iterative to avoid recursion overflow on long trees).
            int[] parent = new int[n];
            Arrays.fill(parent, -1);
            parent[0] = -2;                       // root marker
            int[] order = new int[n];
            int cnt = 0;
            int[] stack = new int[n];
            int sp = 0;
            stack[sp++] = 0;

            while (sp > 0) {
                int u = stack[--sp];
                order[cnt++] = u;
                for (int w : adj[u]) {
                    if (parent[w] == -1) {
                        parent[w] = u;
                        stack[sp++] = w;
                    }
                }
            }

            // dp0[u] = min cover of subtree rooted at u, u NOT taken.
            // dp1[u] = min cover of subtree rooted at u, u taken.
            int[] dp0 = new int[n];
            int[] dp1 = new int[n];

            for (int i = n - 1; i >= 0; i--) { // children before parents
                int u = order[i];
                int s0 = 0, s1 = 0;
                for (int w : adj[u]) {
                    if (parent[w] == u) {       // w is a child of u
                        s0 += dp1[w];
                        s1 += Math.min(dp0[w], dp1[w]);
                    }
                }
                dp0[u] = s0;                    // u not taken: all children taken
                dp1[u] = 1 + s1;                // u taken: children free
            }
            return Math.min(dp0[0], dp1[0]);
        }

        // -------------------------------------------------------------------
        // K_BIPARTITE: min vertex cover = max matching (Konig), Hopcroft-Karp.
        // Colors: 0 = left, 1 = right.
        // -------------------------------------------------------------------
        private int minVertexCoverBipartite(int[][] adj, int n, int[] color) {
            final int NIL = n;                  // sentinel vertex (index n)

            // Collect the "left" part (color 0).
            int nL = 0;
            for (int i = 0; i < n; i++) if (color[i] == 0) nL++;
            int[] left = new int[nL];
            int p = 0;
            for (int i = 0; i < n; i++) if (color[i] == 0) left[p++] = i;

            int[] pairU = new int[n + 1];       // L vertex -> matched R vertex (or NIL)
            int[] pairV = new int[n + 1];       // R vertex -> matched L vertex (or NIL)
            int[] dist = new int[n + 1];        // layer of left vertices (+NIL)
            Arrays.fill(pairU, NIL);
            Arrays.fill(pairV, NIL);

            int matching = 0;
            while (hkBfs(pairU, pairV, left, adj, NIL, dist)) {
                for (int u : left) {
                    if (pairU[u] == NIL && hkDfs(u, pairU, pairV, adj, NIL, dist)) {
                        matching++;
                    }
                }
            }
            return matching;                    // Konig: min VC size == max matching size
        }

        private boolean hkBfs(int[] pairU, int[] pairV, int[] left, int[][] adj,
                              int NIL, int[] dist) {
            final int INF = Integer.MAX_VALUE / 2;
            Arrays.fill(dist, INF);             // <-- critical: fresh dist each phase
            ArrayDeque<Integer> q = new ArrayDeque<>();
            for (int u : left) {
                if (pairU[u] == NIL) { dist[u] = 0; q.add(u); }
            }
            dist[NIL] = INF;
            while (!q.isEmpty()) {
                int u = q.poll();
                if (dist[u] < dist[NIL]) {
                    for (int v : adj[u]) {
                        int pu = pairV[v];      // left vertex matched to v (possibly NIL)
                        if (dist[pu] == INF) {
                            dist[pu] = dist[u] + 1;
                            q.add(pu);
                        }
                    }
                }
            }
            return dist[NIL] != INF;
        }

        private boolean hkDfs(int u, int[] pairU, int[] pairV, int[][] adj,
                              int NIL, int[] dist) {
            final int INF = Integer.MAX_VALUE / 2;
            if (u != NIL) {
                for (int v : adj[u]) {
                    int pu = pairV[v];
                    if (dist[pu] == dist[u] + 1) {
                        if (hkDfs(pu, pairU, pairV, adj, NIL, dist)) {
                            pairV[v] = u;
                            pairU[u] = v;
                            return true;
                        }
                    }
                }
                dist[u] = INF;                  // prune dead ends
                return false;
            }
            return true;
        }

        // -------------------------------------------------------------------
        // Unstructured fallback: exhaustive search over all 2^V subsets.
        // -------------------------------------------------------------------
        private int minVertexCoverBruteForce(int[][] adj, int n) {
            int best = n;
            long total = 1L << n;
            for (long mask = 0; mask < total; mask++) {
                int bits = Long.bitCount(mask);
                if (bits >= best) continue;     // cannot improve
                boolean covers = true;
                outer:
                for (int u = 0; u < n; u++) {
                    for (int w : adj[u]) {
                        if (u < w) {            // consider each edge once
                            boolean bitU = ((mask >> u) & 1L) == 1L;
                            boolean bitW = ((mask >> w) & 1L) == 1L;
                            if (!bitU && !bitW) { covers = false; break outer; }
                        }
                    }
                }
                if (covers) best = bits;
            }
            return best;
        }
    }

    // --- Main Benchmark & Software Engineering Demonstration -------------

    public static void main(String[] args) {
        System.out.println("================================================================");
        System.out.println(" DESIGN-BY-CONTRACT & PARAMETRIC COMPLEXITY (P_u[K]) DEMONSTRATION");
        System.out.println("                                    -- Vertex Cover problem --");
        System.out.println("================================================================\n");

        ParametricVertexCoverSolver solver = new ParametricVertexCoverSolver();

        // ---- Test 1: Huge TREE (path) -> linear DP collapse -> SLA met.
        int T = 500_000;
        System.out.println("--> Test 1: Processing a TREE with V = " + String.format("%,d", T)
                + " vertices (K_TREE)...");
        int[][] path = buildPath(T);
        ExecutionReport r1 = solver.solveSlaGuaranteed(path);
        printReport(r1);

        // ---- Test 2: Large even cycle (bipartite, NOT a tree) -> Konig/HK.
        int C = 40_000; // even, so bipartite
        System.out.println("--> Test 2: Processing a BIPARTITE graph with V = " + String.format("%,d", C)
                + " vertices (even cycle, K_BIPARTITE)...");
        int[][] cycle = buildEvenCycle(C);
        ExecutionReport r2 = solver.solveSlaGuaranteed(cycle);
        printReport(r2);

        // ---- Test 3: Small unstructured non-bipartite graph -> brute force.
        System.out.println("--> Test 3: Testing small unstructured non-bipartite graph (K = \\epsilon, triangle)...");
        int[][] triangle = new int[][]{
            {1, 2},
            {0, 2},
            {0, 1}
        };
        ExecutionReport r3 = solver.solveSlaGuaranteed(triangle);
        printReport(r3);

        // ---- Test 4: Large unstructured non-bipartite graph -> SLA rejection.
        System.out.println("--> Test 4: Attempting large non-bipartite graph (V = 200, K = \\epsilon)...");
        int[][] nonBip = buildNonBipartite(200);
        try {
            solver.solveSlaGuaranteed(nonBip);
        } catch (SlaBreachException e) {
            System.out.println("  [CONTRACT REJECTION TRIGGERED]");
            System.out.println("  Exception Message: " + e.getMessage());
            System.out.println("  SLA Status       : PROTECTED (System prevented unbounded CPU execution!)\n");
        }

        System.out.println("================================================================");
        System.out.println(" SUMMARY OF PRACTICAL VALUE:");
        System.out.println(" 1. Verifying property K in O(V+E) collapses NP-hard Vertex Cover to polynomial.");
        System.out.println(" 2. A 500,000-vertex tree and a 40,000-vertex bipartite graph are solved exactly,");
        System.out.println("    whereas brute force would need 2^V time.");
        System.out.println(" 3. Unstructured non-bipartite inputs are rejected upfront, guaranteeing deterministic latency.");
        System.out.println("================================================================\n");
    }

    private static void printReport(ExecutionReport r) {
        System.out.printf("  - Min Vertex Cover   : %d%n", r.getCoverSize());
        System.out.printf("  - #Vertices          : %s%n", String.format("%,d", r.getNumVertices()));
        System.out.printf("  - #Edges             : %s%n", String.format("%,d", r.getNumEdges()));
        System.out.printf("  - Matched Property K : %s%n", r.getMatchedPropertyK());
        System.out.printf("  - Guard Verify Time  : %.3f ms (C_verify(K) linear scan)%n", r.getVerificationTimeNanos() / 1_000_000.0);
        System.out.printf("  - Solver Exec Time   : %.6f ms (UP[K] collapse)%n", r.getExecutionTimeNanos() / 1_000_000.0);
        System.out.printf("  - Total Time         : %.3f ms%n", r.getTotalTimeNanos() / 1_000_000.0);
        System.out.printf("  - SLA Status         : %s%n%n", r.isSlaGuaranteed() ? "PASSED [SLA MET]" : "FAILED [SLA BREACHED]");
    }

    /** A path P_n (a tree): vertices 0..n-1, edges (i, i+1). */
    private static int[][] buildPath(int n) {
        int[][] adj = new int[n][];
        for (int i = 0; i < n; i++) {
            int left = (i > 0) ? 1 : 0;
            int right = (i < n - 1) ? 1 : 0;
            adj[i] = new int[left + right];
            int c = 0;
            if (left  == 1) adj[i][c++] = i - 1;
            if (right == 1) adj[i][c++] = i + 1;
        }
        return adj;
    }

    /** An even cycle C_n (bipartite, NOT a tree): edges (i, i+1 mod n). */
    private static int[][] buildEvenCycle(int n) {
        int[][] adj = new int[n][];
        for (int i = 0; i < n; i++) {
            adj[i] = new int[]{(i - 1 + n) % n, (i + 1) % n};
        }
        return adj;
    }

    /** A connected non-bipartite graph: a path plus one chord making an odd cycle. */
    private static int[][] buildNonBipartite(int n) {
        // Path 0-1-2-...-n-1  PLUS edge (0,2) => triangle 0-1-2 => odd cycle.
        // m = (n-1) + 1 = n, connected, non-bipartite.
        int[][] adj = new int[n][];
        for (int u = 0; u < n; u++) {
            int deg = 0;
            if (u > 0) deg++;          // edge to u-1
            if (u < n - 1) deg++;      // edge to u+1
            if (u == 0 && n > 2) deg++;   // chord 0-2
            if (u == 2) deg++;            // chord 0-2
            adj[u] = new int[deg];
        }
        for (int u = 0; u < n; u++) {
            int c = 0;
            if (u > 0) adj[u][c++] = u - 1;
            if (u < n - 1) adj[u][c++] = u + 1;
            if (u == 0 && n > 2) adj[u][c++] = 2;
            if (u == 2) adj[u][c++] = 0;
        }
        return adj;
    }
}
