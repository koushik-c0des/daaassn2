#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <queue>
#include <cmath>
#include <climits>
#include <functional>
#include <chrono>

using namespace std;
using namespace std::chrono;

// Structure to represent the graph
struct Graph {
    int n; // Number of vertices
    int m; // Number of edges
    vector<unordered_set<int>> adj; // Adjacency list using sets for faster lookup
};

// Structure for the flow network
struct FlowGraph {
    int n;
    vector<vector<int>> capacity;
    vector<vector<int>> flow;
    vector<vector<int>> adj;
};

// Function declarations
Graph loadGraph(const string& filename);
vector<vector<int>> findAllHMinusOneCliques(const Graph& graph, int h);
bool formsHClique(const Graph& graph, const vector<int>& hMinusOneClique, int vertex);
int maxDegreeInGraph(const Graph& graph);
int countHCliquesInSubgraph(const Graph& graph, const vector<int>& subgraph, int h);
vector<int> findCDSExact(const Graph& graph, int h);

// Find maximum degree in the graph
int maxDegreeInGraph(const Graph& graph) {
    int maxDegree = 0;
    int v = 0;
    while (v < graph.n) {
        maxDegree = max(maxDegree, (int)graph.adj[v].size());
        v++;
    }
    return maxDegree;
}

// Check if a vertex forms an h-clique with the given (h-1)-clique
bool formsHClique(const Graph& graph, const vector<int>& hMinusOneClique, int vertex) {
    int i = 0;
    while (i < hMinusOneClique.size()) {
        int v = hMinusOneClique[i];
        if (graph.adj[vertex].find(v) == graph.adj[vertex].end()) {
            return false;
        }
        i++;
    }
    return true;
}

// Graph loading function
Graph loadGraph(const string& filename) {
    // First pass: find all unique vertices and determine the real n
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "Error opening file: " << filename << endl;
        exit(1);
    }

    int n, m;
    file >> n >> m;
    
    // Read all edges to find actual vertices used
    unordered_set<int> uniqueVertices;
    int u, v;
    int i = 0;
    while (i < m) {
        file >> u >> v;
        uniqueVertices.insert(u);
        uniqueVertices.insert(v);
        i++;
    }
    
    // Create remapping
    unordered_map<int, int> nodeRemap;
    int newId = 0;
    for (int vertex : uniqueVertices) {
        nodeRemap[vertex] = newId++;
    }
    
    // Reopen file and build graph with remapped IDs
    file.close();
    file.open(filename);
    file >> n >> m;
    
    Graph graph;
    graph.n = uniqueVertices.size();
    graph.m = 0; // Will count actual added edges
    graph.adj.resize(graph.n);
    
    i = 0;
    while (i < m) {
        file >> u >> v;
        int remappedU = nodeRemap[u];
        int remappedV = nodeRemap[v];
        
        // Avoid self-loops and double-counting edges
        if (remappedU != remappedV && 
            graph.adj[remappedU].find(remappedV) == graph.adj[remappedU].end()) {
            graph.adj[remappedU].insert(remappedV);
            graph.adj[remappedV].insert(remappedU);
            graph.m++;
        }
        i++;
    }
    
    cout << "Remapped " << uniqueVertices.size() << " vertices to range 0-" << (graph.n-1) << endl;
    return graph;
}


// Calculate the degree of vertex v with respect to pattern Ψ (number of h-cliques containing v)
int degreeWithRespectToPattern(const Graph& graph, int vertex, int h) {
    // For this implementation, we'll count how many h-cliques contain this vertex
    vector<int> allVertices;
    int i = 0;
    while (i < graph.n) {
        allVertices.push_back(i);
        i++;
    }
    
    int count = 0;
    vector<int> current = {vertex};
    
    function<void(int, int)> enumerateCliques = [&](int start, int size) {
        if (size == h) {
            count++;
            return;
        }
        
        int i = start;
        while (i < graph.n) {
            int v = allVertices[i];
            if (v == vertex) {
                i++;
                continue;
            }
            
            bool canAdd = true;
            int j = 0;
            while (j < current.size()) {
                int u = current[j];
                if (graph.adj[u].find(v) == graph.adj[u].end()) {
                    canAdd = false;
                    break;
                }
                j++;
            }
            
            if (canAdd) {
                current.push_back(v);
                enumerateCliques(i + 1, size + 1);
                current.pop_back();
            }
            i++;
        }
    };
    
    enumerateCliques(0, 1); // Start from size 1 since vertex is already in current
    return count;
}

// Count the number of h-cliques in a subgraph
int countHCliquesInSubgraph(const Graph& graph, const vector<int>& subgraph, int h) {
    if (subgraph.empty() || subgraph.size() < h) return 0;
    
    unordered_set<int> subgraphSet(subgraph.begin(), subgraph.end());
    vector<int> current;
    int count = 0;
    
    function<void(int, int)> enumerateCliques = [&](int start, int size) {
        if (size == h) {
            count++;
            return;
        }
        
        int i = start;
        while (i < subgraph.size()) {
            int v = subgraph[i];
            bool canAdd = true;
            
            int j = 0;
            while (j < current.size()) {
                int u = current[j];
                if (graph.adj[u].find(v) == graph.adj[u].end()) {
                    canAdd = false;
                    break;
                }
                j++;
            }
            
            if (canAdd) {
                current.push_back(v);
                enumerateCliques(i + 1, size + 1);
                current.pop_back();
            }
            i++;
        }
    };
    
    enumerateCliques(0, 0);
    return count;
}

// Function to find all (h-1)-cliques in the graph
vector<vector<int>> findAllHMinusOneCliques(const Graph& graph, int h) {
    vector<vector<int>> hMinusOneCliques;
    
    if (h == 2) {
        // For h=2, (h-1)-cliques are just vertices
        int v = 0;
        while (v < graph.n) {
            hMinusOneCliques.push_back({v});
            v++;
        }
        return hMinusOneCliques;
    }
    
    if (h == 3) {
        // For h=3, (h-1)-cliques are edges
        int v = 0;
        while (v < graph.n) {
            auto it = graph.adj[v].begin();
            while (it != graph.adj[v].end()) {
                int u = *it;
                if (u > v) { // Avoid counting edges twice
                    hMinusOneCliques.push_back({v, u});
                }
                ++it;
            }
            v++;
        }
        return hMinusOneCliques;
    }
    
    // For h>=4, recursively find (h-2)-cliques and extend them
    vector<vector<int>> hMinusTwoCliques = findAllHMinusOneCliques(graph, h-1);
    
    int cliqueIndex = 0;
    while (cliqueIndex < hMinusTwoCliques.size()) {
        const auto& clique = hMinusTwoCliques[cliqueIndex];
        int lastVertex = clique.back();
        
        // Try to extend the clique with vertices adjacent to all vertices in the clique
        int v = lastVertex + 1;
        while (v < graph.n) {
            bool canAdd = true;
            
            int j = 0;
            while (j < clique.size()) {
                int u = clique[j];
                if (graph.adj[u].find(v) == graph.adj[u].end()) {
                    canAdd = false;
                    break;
                }
                j++;
            }
            
            if (canAdd) {
                vector<int> newClique = clique;
                newClique.push_back(v);
                hMinusOneCliques.push_back(newClique);
            }
            v++;
        }
        cliqueIndex++;
    }
    
    return hMinusOneCliques;
}

// Algorithm 1: Exact algorithm for finding CDS
vector<int> findCDSExact(const Graph& graph, int h) {
    // Step 1: Initialize l, u
    double l = 0;
    
    // Calculate maximum degree with respect to pattern (h-cliques)
    int maxDeg = 0;
    int v = 0;
    while (v < graph.n) {
        int deg = degreeWithRespectToPattern(graph, v, h);
        maxDeg = max(maxDeg, deg);
        v++;
    }
    double u = maxDeg;
    
    cout << "Initial bounds: l=" << l << ", u=" << u << endl;
    
    // Step 2: Find all (h-1)-cliques
    vector<vector<int>> hMinusOneCliques = findAllHMinusOneCliques(graph, h);
    cout << "Found " << hMinusOneCliques.size() << " (h-1)-cliques" << endl;
    
    vector<int> densestSubgraph;
    double epsilon = 1.0 / (graph.n * (graph.n - 1));
    
    // Step 3-18: Binary search for optimal alpha
    while (u - l >= epsilon) {
        // Step 4: Set alpha to mid-point
        double alpha = (l + u) / 2.0;
        cout << "Trying alpha = " << alpha << endl;
        
        // Step 5-15: Build flow network
        FlowGraph fg;
        int s = 0; // Source
        int t = 1 + graph.n + hMinusOneCliques.size(); // Sink
        fg.n = t + 1;
        
        fg.capacity.resize(fg.n, vector<int>(fg.n, 0));
        fg.flow.resize(fg.n, vector<int>(fg.n, 0));
        fg.adj.resize(fg.n);
        
        // Steps 6-8: Add edges from source to vertices and vertices to sink
        int v = 0;
        while (v < graph.n) {
            int nodeV = v + 1; // +1 because s=0
            
            // Edge s->v with capacity deg(v, Ψ)
            int degV = degreeWithRespectToPattern(graph, v, h);
            fg.capacity[s][nodeV] = degV;
            fg.adj[s].push_back(nodeV);
            fg.adj[nodeV].push_back(s);
            
            // Edge v->t with capacity alpha*|VΨ|
            int capacity = static_cast<int>(alpha * graph.n); // Using n as |VΨ|
            fg.capacity[nodeV][t] = capacity;
            fg.adj[nodeV].push_back(t);
            fg.adj[t].push_back(nodeV);
            
            v++;
        }
        
        // Steps 9-15: Add edges for (h-1)-cliques
        int cliqueOffset = graph.n + 1;
        
        // Steps 9-11: Add edges from cliques to vertices
        int i = 0;
        while (i < hMinusOneCliques.size()) {
            int cliqueNode = cliqueOffset + i;
            
            int j = 0;
            while (j < hMinusOneCliques[i].size()) {
                int v = hMinusOneCliques[i][j];
                int vertexNode = v + 1;
                
                // Edge ψ->v with infinite capacity
                fg.capacity[cliqueNode][vertexNode] = INT_MAX;
                fg.adj[cliqueNode].push_back(vertexNode);
                fg.adj[vertexNode].push_back(cliqueNode);
                
                j++;
            }
            
            i++;
        }
        
        // Steps 12-15: Add edges from vertices to cliques
        i = 0;
        while (i < hMinusOneCliques.size()) {
            int cliqueNode = cliqueOffset + i;
            const auto& clique = hMinusOneCliques[i];
            
            int v = 0;
            while (v < graph.n) {
                int vertexNode = v + 1;
                
                // Check if v and the clique form an h-clique
                if (formsHClique(graph, clique, v)) {
                    // Edge v->ψ with capacity 1
                    fg.capacity[vertexNode][cliqueNode] = 1;
                    fg.adj[vertexNode].push_back(cliqueNode);
                    fg.adj[cliqueNode].push_back(vertexNode);
                }
                v++;
            }
            
            i++;
        }
        
        // Step 16: Find minimum s-t cut
        // Ford-Fulkerson algorithm for max flow
        auto fordFulkerson = [](FlowGraph& fg, int s, int t) -> int {
            int maxFlow = 0;
            
            while (true) {
                vector<int> parent(fg.n, -1);
                queue<int> q;
                q.push(s);
                parent[s] = s;
                
                while (!q.empty() && parent[t] == -1) {
                    int u = q.front();
                    q.pop();
                    
                    int i = 0;
                    while (i < fg.adj[u].size()) {
                        int v = fg.adj[u][i];
                        if (parent[v] == -1 && fg.capacity[u][v] > fg.flow[u][v]) {
                            parent[v] = u;
                            q.push(v);
                        }
                        i++;
                    }
                }
                
                if (parent[t] == -1) break;
                
                int pathFlow = INT_MAX;
                int v = t;
                while (v != s) {
                    int u = parent[v];
                    pathFlow = min(pathFlow, fg.capacity[u][v] - fg.flow[u][v]);
                    v = parent[v];
                }
                
                v = t;
                while (v != s) {
                    int u = parent[v];
                    fg.flow[u][v] += pathFlow;
                    fg.flow[v][u] -= pathFlow;
                    v = parent[v];
                }
                
                maxFlow += pathFlow;
            }
            
            return maxFlow;
        };
        
        // Function to find the minimum cut (S, T)
        auto findMinCut = [](FlowGraph& fg, int s) -> vector<bool> {
            vector<bool> visited(fg.n, false);
            queue<int> q;
            q.push(s);
            visited[s] = true;
            
            while (!q.empty()) {
                int u = q.front();
                q.pop();
                
                int i = 0;
                while (i < fg.adj[u].size()) {
                    int v = fg.adj[u][i];
                    if (!visited[v] && fg.capacity[u][v] > fg.flow[u][v]) {
                        visited[v] = true;
                        q.push(v);
                    }
                    i++;
                }
            }
            
            return visited;
        };
        
        // Calculate max flow
        fordFulkerson(fg, s, t);
        
        // Find min cut
        vector<bool> inCut = findMinCut(fg, s);
        
        // Step 17-18: Update bounds and densest subgraph
        bool onlySource = true;
        i = 1;
        while (i < fg.n - 1) {
            if (inCut[i]) {
                onlySource = false;
                break;
            }
            i++;
        }
        
        if (onlySource) {
            // Step 17: S = {s}
            u = alpha;
            cout << "Cut contains only source, decreasing upper bound to " << u << endl;
        } else {
            // Step 18: Update lower bound and densest subgraph
            l = alpha;
            
            // Extract the subgraph induced by S\{s}
            densestSubgraph.clear();
            int v = 0;
            while (v < graph.n) {
                int nodeV = v + 1;
                if (inCut[nodeV]) {
                    densestSubgraph.push_back(v);
                }
                v++;
            }
            
            cout << "Cut contains " << densestSubgraph.size() << " vertices, increasing lower bound to " << l << endl;
        }
    }
    
    // Step 19: Return the densest subgraph
    return densestSubgraph;
}

// Main function
int main(int argc, char* argv[]) {
    if (argc != 3) {
        cerr << "Usage: " << argv[0] << " <graph_file> <h>" << endl;
        return 1;
    }
   
    string filename = argv[1];
    int h = stoi(argv[2]);
   
    if (h < 2) {
        cerr << "Error: h must be at least 2" << endl;
        return 1;
    }
   
    // Start timing
    auto start_time = high_resolution_clock::now();
   
    Graph graph = loadGraph(filename);
    cout << "Graph loaded: " << graph.n << " nodes, " << graph.m << " edges" << endl;
   
    // Use the exact algorithm to find CDS
    vector<int> densestSubgraph = findCDSExact(graph, h);
    
    int hCliques = countHCliquesInSubgraph(graph, densestSubgraph, h);
    double density = 0;
    if (!densestSubgraph.empty()) {
        density = (double)hCliques / densestSubgraph.size();
    }
   
    // End timing
    auto end_time = high_resolution_clock::now();
    auto duration = duration_cast<milliseconds>(end_time - start_time);
   
    cout << "Densest subgraph (" << h << "-clique-density):" << endl;
    cout << "Nodes: " << densestSubgraph.size() << endl;
    cout << h << "-cliques: " << hCliques << endl;
    cout << "Density: " << density << endl;
   
    cout << "Node IDs in subgraph:" << endl;
    sort(densestSubgraph.begin(), densestSubgraph.end());
    int i = 0;
    while (i < densestSubgraph.size()) {
        cout << densestSubgraph[i] << " ";
        i++;
    }
    cout << endl;
   
    // Print execution time
    cout << "Execution time: " << duration.count() << " milliseconds" << endl;
   
    return 0;
}
