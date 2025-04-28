#include <iostream>
#include <vector>
#include <queue>
#include <fstream>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <set>
#include <algorithm>
#include <limits>
#include <cmath>
#include <climits>
#include <chrono> 

using namespace std;

// Hash function for pairs
struct pair_hash {
    template <class T1, class T2>
    size_t operator() (const pair<T1, T2>& p) const {
        auto h1 = hash<T1>{}(p.first);
        auto h2 = hash<T2>{}(p.second);
        return h1 ^ h2;
    }
};
struct Graph {
    int n, m;
    vector<vector<int>> adj;
    unordered_map<int, int> id2idx, idx2id;
    vector<pair<int, int>> edges;
};
int count_total_h_subgraphs(const Graph& G, const vector<int>& nodes, int h);
void count_h_cliques(const Graph& G, int h, int start_vertex,
                     vector<int>& current_clique,
                     const unordered_map<int, unordered_set<int>>& adj_set,
                     int& count);
// ----------- Flow Network (Edmonds-Karp) -----------
struct Edge {
    int to, rev;
    int cap;
};

class FlowNetwork {
public:
    int N;
    vector<vector<Edge>> adj;

    FlowNetwork(int N_) : N(N_), adj(N_) {}

    void add_edge(int from, int to, int cap) {
        adj[from].push_back({to, (int)adj[to].size(), cap});
        adj[to].push_back({from, (int)adj[from].size() - 1, 0});
    }

    int bfs(int s, int t, vector<int>& level) {
        fill(level.begin(), level.end(), -1);
        queue<int> q;
        level[s] = 0;
        q.push(s);
        while (!q.empty()) {
            int v = q.front(); q.pop();
            int i = 0;
            while (i < adj[v].size()) {
                const auto& e = adj[v][i];
                if (e.cap > 0 && level[e.to] < 0) {
                    level[e.to] = level[v] + 1;
                    q.push(e.to);
                }
                i++;
            }
        }
        return level[t] != -1;
    }

    int dfs(int v, int t, int upTo, vector<int>& level, vector<int>& iter) {
        if (v == t) return upTo;
        while (iter[v] < adj[v].size()) {
            Edge& e = adj[v][iter[v]];
            if (e.cap > 0 && level[v] < level[e.to]) {
                int d = dfs(e.to, t, min(upTo, e.cap), level, iter);
                if (d > 0) {
                    e.cap -= d;
                    adj[e.to][e.rev].cap += d;
                    return d;
                }
            }
            ++iter[v];
        }
        return 0;
    }

    int max_flow(int s, int t) {
        int flow = 0;
        vector<int> level(N), iter(N);
        while (bfs(s, t, level)) {
            fill(iter.begin(), iter.end(), 0);
            int f;
            while ((f = dfs(s, t, INT_MAX, level, iter)) > 0) {
                flow += f;
            }
        }
        return flow;
    }

    void min_cut(int s, vector<bool>& visited) {
        visited.assign(N, false);
        queue<int> q;
        q.push(s);
        visited[s] = true;
        while (!q.empty()) {
            int u = q.front(); q.pop();
            int i = 0;
            while (i < adj[u].size()) {
                const auto& e = adj[u][i];
                if (e.cap > 0 && !visited[e.to]) {
                    visited[e.to] = true;
                    q.push(e.to);
                }
                i++;
            }
        }
    }
};

Graph read_graph(const string& filename) {
    ifstream fin(filename);
    string line;
    set<int> all_nodes;
    vector<pair<int, int>> raw_edges;
    while (getline(fin, line)) {
        if (line.empty() || line[0] == '#') continue;
        istringstream iss(line);
        int u, v;
        if (!(iss >> u >> v)) continue;
        all_nodes.insert(u); all_nodes.insert(v);
        raw_edges.emplace_back(u, v);
    }
    unordered_map<int, int> id2idx, idx2id;
    int idx = 0;
    auto it = all_nodes.begin();
    while (it != all_nodes.end()) {
        int id = *it;
        id2idx[id] = idx;
        idx2id[idx] = id;
        ++idx;
        ++it;
    }

    int n = all_nodes.size();
    vector<vector<int>> adj(n);
    set<pair<int, int>> edgeset;
    
    int edgeIndex = 0;
    while (edgeIndex < raw_edges.size()) {
        auto& e = raw_edges[edgeIndex];
        int u = id2idx[e.first], v = id2idx[e.second];
        if (u == v) {
            edgeIndex++;
            continue;
        }
        if (u > v) swap(u, v);
        if (!edgeset.insert({u, v}).second) {
            edgeIndex++;
            continue; // avoid duplicates
        }
        adj[u].push_back(v);
        adj[v].push_back(u);
        edgeIndex++;
    }
    
    vector<pair<int, int>> edges(edgeset.begin(), edgeset.end());
    Graph G{n, (int)edges.size(), adj, id2idx, idx2id, edges};
    return G;
}

// ----------- k-core Decomposition -----------
vector<int> core_decomposition(const Graph& G) {
    int n = G.n;
    vector<int> deg(n);
    int u = 0;
    while (u < n) {
        deg[u] = G.adj[u].size();
        ++u;
    }

    vector<int> core(n, 0);
    vector<bool> removed(n, false);
    int remaining = n;

    while (remaining > 0) {
        int min_deg = INT_MAX;
        int min_v = -1;
        int i = 0;
        while (i < n) {
            if (!removed[i] && deg[i] < min_deg) {
                min_deg = deg[i];
                min_v = i;
            }
            ++i;
        }
        if (min_v == -1) break;

        core[min_v] = deg[min_v];
        removed[min_v] = true;
        --remaining;

        auto it = G.adj[min_v].begin();
        while (it != G.adj[min_v].end()) {
            int u = *it;
            if (!removed[u]) deg[u]--;
            ++it;
        }
    }
    return core;
}

// ----------- Helper function for counting h-cliques containing an edge -----------
int count_h_cliques_containing_edge(const Graph& G, int h, int u, int v) {
    if (h == 2) return 1; // Edge itself is a 2-clique
    if (h == 3) {
        // Count triangles containing edge (u,v)
        unordered_set<int> u_neighbors(G.adj[u].begin(), G.adj[u].end());
        int count = 0;
        auto it = G.adj[v].begin();
        while (it != G.adj[v].end()) {
            int w = *it;
            if (u_neighbors.count(w)) count++;
            ++it;
        }
        return count;
    }
   
    // For h > 3, find all (h-2)-cliques in the common neighborhood
    unordered_set<int> common_neighbors;
    unordered_set<int> u_neighbors(G.adj[u].begin(), G.adj[u].end());
    auto it = G.adj[v].begin();
    while (it != G.adj[v].end()) {
        int w = *it;
        if (u_neighbors.count(w)) common_neighbors.insert(w);
        ++it;
    }
   
    if (common_neighbors.size() < h-2) return 0;
   
    // Create subgraph of common neighbors
    int sz = common_neighbors.size();
    vector<int> node_to_idx;
    unordered_map<int, int> idx_map;
    auto it2 = common_neighbors.begin();
    int idx = 0;
    while (it2 != common_neighbors.end()) {
        int node = *it2;
        node_to_idx.push_back(node);
        idx_map[node] = idx++;
        ++it2;
    }
   
    vector<vector<int>> sub_adj(sz);
    int i = 0;
    while (i < sz) {
        int node = node_to_idx[i];
        auto it3 = G.adj[node].begin();
        while (it3 != G.adj[node].end()) {
            int neigh = *it3;
            if (common_neighbors.count(neigh)) {
                sub_adj[i].push_back(idx_map[neigh]);
            }
            ++it3;
        }
        ++i;
    }
   
    // Count (h-2)-cliques in this subgraph
    Graph sub_G = {sz, 0, sub_adj, {}, {}, {}};
    vector<int> sub_nodes(sz);
    i = 0;
    while (i < sz) {
        sub_nodes[i] = i;
        ++i;
    }
   
    int count = 0;
    if (h == 4) {
        // For 4-cliques, count edges in the common neighborhood
        i = 0;
        while (i < sz) {
            auto it4 = sub_adj[i].begin();
            while (it4 != sub_adj[i].end()) {
                int j = *it4;
                if (i < j) count++;
                ++it4;
            }
            ++i;
        }
    } else {
        // For h > 4, recursively count (h-2)-cliques
        count = count_total_h_subgraphs(sub_G, sub_nodes, h-2);
    }
   
    return count;
}

// Forward declaration of the recursive clique counting function
void count_cliques_containing_vertex(
    const Graph& G, int h, int start_vertex,
    vector<int>& current_clique,
    const unordered_map<int, unordered_set<int>>& adj_set,
    vector<int>& h_count);

// ----------- h-Subgraph Counting -----------
// Count number of h-subgraphs containing each vertex
vector<int> count_h_subgraphs(const Graph& G, int h, const vector<int>& nodes = {}) {
    int n = G.n;
    vector<int> node_list;
    if (nodes.empty()) {
        node_list.resize(n);
        int i = 0;
        while (i < n) {
            node_list[i] = i;
            i++;
        }
    } else {
        node_list = nodes;
    }
   
    vector<int> h_count(n, 0);
   
    if (h == 2) {  // Edges
        unordered_set<int> node_set(node_list.begin(), node_list.end());
        int i = 0;
        while (i < node_list.size()) {
            int u = node_list[i];
            int j = 0;
            while (j < G.adj[u].size()) {
                int v = G.adj[u][j];
                if (u < v && node_set.count(v)) {
                    h_count[u]++;
                    h_count[v]++;
                }
                j++;
            }
            i++;
        }
    } else if (h == 3) {  // Triangles
        unordered_map<int, unordered_set<int>> adj_set;
        int i = 0;
        while (i < node_list.size()) {
            int u = node_list[i];
            adj_set[u] = unordered_set<int>(G.adj[u].begin(), G.adj[u].end());
            i++;
        }
       
        i = 0;
        while (i < node_list.size()) {
            int u = node_list[i];
            int j = 0;
            while (j < G.adj[u].size()) {
                int v = G.adj[u][j];
                if (u >= v) {
                    j++;
                    continue;  // Count each edge once
                }
                int k = 0;
                while (k < G.adj[v].size()) {
                    int w = G.adj[v][k];
                    if (v >= w) {
                        k++;
                        continue;  // Count each edge once
                    }
                    if (adj_set[u].count(w)) {  // Found a triangle
                        h_count[u]++;
                        h_count[v]++;
                        h_count[w]++;
                    }
                    k++;
                }
                j++;
            }
            i++;
        }
    } else {  // h >= 4
        unordered_map<int, unordered_set<int>> adj_set;
        int i = 0;
        while (i < node_list.size()) {
            int u = node_list[i];
            adj_set[u] = unordered_set<int>();
            int j = 0;
            while (j < G.adj[u].size()) {
                int v = G.adj[u][j];
                if (find(node_list.begin(), node_list.end(), v) != node_list.end()) {
                    adj_set[u].insert(v);
                }
                j++;
            }
            i++;
        }
       
        // For each node, count h-cliques it's part of
        i = 0;
        while (i < node_list.size()) {
            int u = node_list[i];
            // Start with the node u and extend to h-cliques
            vector<int> current_clique = {u};
            count_cliques_containing_vertex(G, h, u, current_clique, adj_set, h_count);
            i++;
        }
    }
   
    return h_count;
}

// Helper function to recursively count h-cliques
void count_cliques_containing_vertex(
    const Graph& G, int h, int start_vertex,
    vector<int>& current_clique,
    const unordered_map<int, unordered_set<int>>& adj_set,
    vector<int>& h_count) {
   
    if (current_clique.size() == h) {
        // Found an h-clique, increment count for all vertices in it
        int i = 0;
        while (i < current_clique.size()) {
            int v = current_clique[i];
            h_count[v]++;
            i++;
        }
        return;
    }
   
    // Find potential candidates to extend current clique
    unordered_set<int> candidates;
    if (current_clique.size() == 1) {
        // First level: all neighbors of start_vertex are candidates
        auto it = adj_set.at(start_vertex).begin();
        while (it != adj_set.at(start_vertex).end()) {
            int v = *it;
            if (v > start_vertex) { // To avoid counting the same clique multiple times
                candidates.insert(v);
            }
            ++it;
        }
    } else {
        // Intersect neighborhood of all vertices in current clique
        candidates = adj_set.at(current_clique[0]);
        size_t i = 1;
        while (i < current_clique.size()) {
            unordered_set<int> temp;
            auto it = candidates.begin();
            while (it != candidates.end()) {
                int v = *it;
                if (adj_set.at(current_clique[i]).count(v)) {
                    temp.insert(v);
                }
                ++it;
            }
            candidates = temp;
            i++;
        }
       
        // Filter candidates to ensure they're greater than the start vertex
        // and the last vertex in current_clique (to ensure unique counting)
        unordered_set<int> filtered_candidates;
        auto it = candidates.begin();
        while (it != candidates.end()) {
            int v = *it;
            if (v > start_vertex && v > current_clique.back()) {
                filtered_candidates.insert(v);
            }
            ++it;
        }
        candidates = filtered_candidates;
    }
   
    // Extend the clique with each candidate
    auto it = candidates.begin();
    while (it != candidates.end()) {
        int v = *it;
        current_clique.push_back(v);
        count_cliques_containing_vertex(G, h, start_vertex, current_clique, adj_set, h_count);
        current_clique.pop_back();
        ++it;
    }
}

// Count total h-subgraphs in a subgraph
int count_total_h_subgraphs(const Graph& G, const vector<int>& nodes, int h) {
    if (nodes.empty()) return 0;
    unordered_set<int> node_set(nodes.begin(), nodes.end());
   
    if (h == 2) {  // Edges
        int edge_count = 0;
        int i = 0;
        while (i < nodes.size()) {
            int u = nodes[i];
            int j = 0;
            while (j < G.adj[u].size()) {
                int v = G.adj[u][j];
                if (u < v && node_set.count(v)) {
                    edge_count++;
                }
                j++;
            }
            i++;
        }
        return edge_count;
    } else if (h == 3) {  // Triangles
        int triangle_count = 0;
        unordered_map<int, unordered_set<int>> adj_set;
        int i = 0;
        while (i < nodes.size()) {
            int u = nodes[i];
            adj_set[u] = unordered_set<int>();
            int j = 0;
            while (j < G.adj[u].size()) {
                int v = G.adj[u][j];
                if (node_set.count(v)) {
                    adj_set[u].insert(v);
                }
                j++;
            }
            i++;
        }
       
        i = 0;
        while (i < nodes.size()) {
            int u = nodes[i];
            auto it = adj_set[u].begin();
            while (it != adj_set[u].end()) {
                int v = *it;
                if (u >= v) {
                    ++it;
                    continue;
                }
                auto it2 = adj_set[v].begin();
                while (it2 != adj_set[v].end()) {
                    int w = *it2;
                    if (v >= w) {
                        ++it2;
                        continue;
                    }
                    if (adj_set[u].count(w)) {  // Found a triangle
                        triangle_count++;
                    }
                    ++it2;
                }
                ++it;
            }
            i++;
        }
        return triangle_count;
    } else {  // h ≥ 4
        // Create adjacency set for the nodes
        unordered_map<int, unordered_set<int>> adj_set;
        int i = 0;
        while (i < nodes.size()) {
            int u = nodes[i];
            adj_set[u] = unordered_set<int>();
            int j = 0;
            while (j < G.adj[u].size()) {
                int v = G.adj[u][j];
                if (node_set.count(v)) {
                    adj_set[u].insert(v);
                }
                j++;
            }
            i++;
        }
       
        int clique_count = 0;
        i = 0;
        while (i < nodes.size()) {
            int u = nodes[i];
            vector<int> clique = {u};
            count_h_cliques(G, h, u, clique, adj_set, clique_count);
            i++;
        }
       
        // Each h-clique is counted exactly once
        return clique_count / h;
    }
}

// Helper function to count h-cliques for total count
void count_h_cliques(const Graph& G, int h, int start_vertex,
                     vector<int>& current_clique,
                     const unordered_map<int, unordered_set<int>>& adj_set,
                     int& count) {
   
    if (current_clique.size() == h) {
        // Found an h-clique
        count += h; // Add h to count (will be divided by h later)
        return;
    }
   
    // Find candidates to extend current clique
    unordered_set<int> candidates;
    if (current_clique.size() == 1) {
        // First level: all neighbors of start_vertex are candidates
        auto it = adj_set.at(start_vertex).begin();
        while (it != adj_set.at(start_vertex).end()) {
            int v = *it;
            if (v > start_vertex) { // To avoid counting the same clique multiple times
                candidates.insert(v);
            }
            ++it;
        }
    } else {
        // Intersect neighborhood of all vertices in current clique
        candidates = adj_set.at(current_clique[0]);
        size_t i = 1;
        while (i < current_clique.size()) {
            unordered_set<int> temp;
            auto it = candidates.begin();
            while (it != candidates.end()) {
                int v = *it;
                if (adj_set.at(current_clique[i]).count(v)) {
                    temp.insert(v);
                }
                ++it;
            }
            candidates = temp;
            i++;
        }
       
        // Filter candidates
        unordered_set<int> filtered_candidates;
        auto it = candidates.begin();
        while (it != candidates.end()) {
            int v = *it;
            if (v > start_vertex && v > current_clique.back()) {
                filtered_candidates.insert(v);
            }
            ++it;
        }
        candidates = filtered_candidates;
    }
   
    // Extend the clique with each candidate
    auto it = candidates.begin();
    while (it != candidates.end()) {
        int v = *it;
        current_clique.push_back(v);
        count_h_cliques(G, h, start_vertex, current_clique, adj_set, count);
        current_clique.pop_back();
        ++it;
    }
}

// ----------- Charikar's peeling algorithm for h-subgraphs -----------
pair<vector<int>, double> charikar_peeling_h(const Graph& G, int h) {
    int n = G.n;
    vector<int> h_count = count_h_subgraphs(G, h);
    vector<int> nodes(n);
    int i = 0;
    while (i < n) {
        nodes[i] = i;
        i++;
    }
   
    vector<bool> removed(n, false);
    vector<int> best_nodes = nodes;
    int total_h_subgraphs = count_total_h_subgraphs(G, nodes, h);
    double best_density = (double)total_h_subgraphs / n;
   
    while (!nodes.empty()) {
        // Find min degree node
        int min_idx = 0;
        i = 1;
        while (i < nodes.size()) {
            if (h_count[nodes[i]] < h_count[nodes[min_idx]]) {
                min_idx = i;
            }
            i++;
        }
       
        int u = nodes[min_idx];
        removed[u] = true;
        nodes.erase(nodes.begin() + min_idx);
       
        // Recalculate h-subgraphs count for remaining nodes
        h_count = count_h_subgraphs(G, h, nodes);
       
        // Calculate density
        if (!nodes.empty()) {
            total_h_subgraphs = count_total_h_subgraphs(G, nodes, h);
            double density = (double)total_h_subgraphs / nodes.size();
            if (density > best_density) {
                best_density = density;
                best_nodes = nodes;
            }
        }
    }
   
    return {best_nodes, best_density};
}

// ----------- CoreExact Algorithm for h-subgraph Density -----------
vector<int> coreexact_densest_h_subgraph(const Graph& G, int h) {
    int n = G.n;
   
    // Step 1: Pruning1 - Charikar's peeling for best lower bound
    auto [best_nodes, best_density] = charikar_peeling_h(G, h);
    double l = best_density;
   
    // Step 2: Pruning2 - restrict to k-core
    vector<int> core = core_decomposition(G);
    int kmax = *max_element(core.begin(), core.end());
    int k_prime = ceil(l);
    vector<bool> in_core(n, false);
    int i = 0;
    while (i < n) {
        if (core[i] >= k_prime) in_core[i] = true;
        i++;
    }
   
    // Find connected components in k'-core
    vector<vector<int>> components;
    vector<bool> visited(n, false);
    i = 0;
    while (i < n) {
        if (in_core[i] && !visited[i]) {
            vector<int> comp;
            queue<int> q; 
            q.push(i); 
            visited[i] = true;
            while (!q.empty()) {
                int u = q.front(); 
                q.pop();
                comp.push_back(u);
                int j = 0;
                while (j < G.adj[u].size()) {
                    int v = G.adj[u][j];
                    if (in_core[v] && !visited[v]) {
                        visited[v] = true;
                        q.push(v);
                    }
                    j++;
                }
            }
            components.push_back(comp);
        }
        i++;
    }
   
    vector<int> best_subgraph = best_nodes;
   
    // Step 3: For each component, run flow-based binary search
    i = 0;
    while (i < components.size()) {
        auto& comp = components[i];
        int sz = comp.size();
        if (sz <= h-1) {
            i++;
            continue;  // Need at least h nodes to form h-subgraph
        }
       
        unordered_map<int, int> idx_map;
        int j = 0;
        while (j < sz) {
            idx_map[comp[j]] = j;
            j++;
        }
       
        // Create subgraph
        vector<vector<int>> sub_adj(sz);
        j = 0;
        while (j < sz) {
            int u = comp[j];
            int k = 0;
            while (k < G.adj[u].size()) {
                int v = G.adj[u][k];
                if (idx_map.count(v)) {
                    sub_adj[j].push_back(idx_map[v]);
                }
                k++;
            }
            j++;
        }
       
        // Count h-subgraphs for each vertex in the component
        vector<int> local_nodes(sz);
        j = 0;
        while (j < sz) {
            local_nodes[j] = j;
            j++;
        }
        Graph sub_G = {sz, 0, sub_adj, {}, {}, {}};
        vector<int> h_count_local = count_h_subgraphs(sub_G, h, local_nodes);
        int total_h_subgraphs = count_total_h_subgraphs(sub_G, local_nodes, h);
       
        // Binary search
        double l2 = l, u2 = (h == 2) ? kmax : total_h_subgraphs;
        if (u2 == 0) u2 = 1; // Avoid division by zero
        vector<int> best_S;
       
        // Precision for binary search
        double epsilon = 1.0 / (sz * (sz - 1));
       
        while (u2 - l2 > epsilon) {
            double alpha = (l2 + u2) / 2.0;
            int N = 2 + sz;  // source=0, sink=1, nodes 2..N-1
            FlowNetwork fn(N);
           
            // Build flow network for different h values
            if (h == 2) {  // Edge density
                // s->v: m
                j = 0;
                while (j < sz) {
                    fn.add_edge(0, 2 + j, total_h_subgraphs);
                    j++;
                }
                // v->t: m + 2*alpha - deg_v
                j = 0;
                while (j < sz) {
                    fn.add_edge(2 + j, 1, (int)round(total_h_subgraphs + 2 * alpha - h_count_local[j]));
                    j++;
                }
                // For each edge (u,v): capacity 1 in both directions
                j = 0;
                while (j < sz) {
                    int k = 0;
                    while (k < sub_adj[j].size()) {
                        int neighbor = sub_adj[j][k];
                        if (j < neighbor) {  // Add each edge once
                            fn.add_edge(2 + j, 2 + neighbor, 1);
                            fn.add_edge(2 + neighbor, 2 + j, 1);
                        }
                        k++;
                    }
                    j++;
                }
            } else {  // h >= 3 (h-cliques)
                // Calculate edge-h-clique associations
                unordered_map<pair<int, int>, int, pair_hash> edge_h_count;
               
                if (h == 3) {  // Triangles
                    // For triangles, count triangles per edge
                    int j = 0;
                    while (j < sz) {
                        int k = 0;
                        while (k < sub_adj[j].size()) {
                            int neighbor = sub_adj[j][k];
                            if (j < neighbor) {
                                edge_h_count[{j, neighbor}] = count_h_cliques_containing_edge(sub_G, h, j, neighbor);
                            }
                            k++;
                        }
                        j++;
                    }
                } else {  // h >= 4
                    // For h>=4, compute how many h-cliques each edge participates in
                    int j = 0;
                    while (j < sz) {
                        int k = 0;
                        while (k < sub_adj[j].size()) {
                            int neighbor = sub_adj[j][k];
                            if (j < neighbor) {
                                edge_h_count[{j, neighbor}] = count_h_cliques_containing_edge(sub_G, h, j, neighbor);
                            }
                            k++;
                        }
                        j++;
                    }
                }
               
                // s->v: total_h
                int j = 0;
                while (j < sz) {
                    fn.add_edge(0, 2 + j, total_h_subgraphs);
                    j++;
                }
                // v->t: total_h + h*alpha - h_degree_v
                j = 0;
                while (j < sz) {
                    fn.add_edge(2 + j, 1, (int)round(total_h_subgraphs + h * alpha - h_count_local[j]));
                    j++;
                }
                // Edge capacities based on h-clique participation
                j = 0;
                while (j < sz) {
                    int k = 0;
                    while (k < sub_adj[j].size()) {
                        int neighbor = sub_adj[j][k];
                        if (j < neighbor) {
                            int capacity = edge_h_count[{j, neighbor}];
                            fn.add_edge(2 + j, 2 + neighbor, capacity);
                            fn.add_edge(2 + neighbor, 2 + j, capacity);
                        }
                        k++;
                    }
                    j++;
                }
            }
           
            // Find min-cut
            int flow = fn.max_flow(0, 1);
            vector<bool> vis;
            fn.min_cut(0, vis);
            vector<int> S;
            int j = 0;
            while (j < sz) {
                if (vis[2 + j]) {
                    S.push_back(comp[j]);
                }
                j++;
            }
           
            if (S.empty()) {
                u2 = alpha;
            } else {
                l2 = alpha;
                best_S = S;
            }
        }
       
        if (!best_S.empty()) {
            int h_count_S = count_total_h_subgraphs(G, best_S, h);
            double dens = (double)h_count_S / best_S.size();
            if (dens > best_density) {
                best_density = dens;
                best_subgraph = best_S;
            }
        }
        
        i++;
    }
   
    return best_subgraph;
}

// ----------- Main -----------
int main(int argc, char* argv[]) {
    if (argc < 3) {
        cout << "Usage: " << argv[0] << " <graph_file> <h>" << endl;
        cout << "  h=2: edge density" << endl;
        cout << "  h=3: triangle density" << endl;
        cout << "  h=4: 4-clique density" << endl;
        cout << "  h>4: h-clique density" << endl;
        return 1;
    }
   
    Graph G = read_graph(argv[1]);
    int h = stoi(argv[2]);
   
    if (h < 2) {
        cerr << "Error: h must be at least 2" << endl;
        return 1;
    }
   
    cout << "Graph loaded: " << G.n << " nodes, " << G.m << " edges" << endl;
    cout << "Finding densest subgraph for h=" << h << " subgraphs..." << endl;
    auto start = chrono::high_resolution_clock::now();
    vector<int> subgraph = coreexact_densest_h_subgraph(G, h);
   
    cout << "Densest subgraph (h=" << h << "-subgraph density, CoreExact):" << endl;
    cout << "Nodes: " << subgraph.size() << endl;
    
    int h_count = count_total_h_subgraphs(G, subgraph, h);

    cout << h << "-subgraphs: " << h_count << endl;
    cout << "Density: " << (double)h_count / subgraph.size() << endl;
    cout << "Node IDs in subgraph:" << endl;
    
    int i = 0;
    while (i < subgraph.size()) {
        cout << G.idx2id[subgraph[i]] << " ";
        i++;
    }
    cout << endl;
    
    auto end = chrono::high_resolution_clock::now();
    chrono::duration<double> elapsed = end - start;
  
    cout << "\nExecution time: " << fixed  << elapsed.count()
        << " seconds" << endl;
    return 0;
}
