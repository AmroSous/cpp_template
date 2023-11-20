/*
    Author: Amro Sous
*/
#include<bits/stdc++.h> 
using namespace std; 
#define fastio ios_base::sync_with_stdio(false), cin.tie(nullptr);
#define TxtFile freopen("input.txt","r",stdin)
#define nl "\n"
typedef long long ll;

/*-------------------------------------------------------------------------------------------------*/
/*=======================================>> Number Theory <<=======================================*/
/*-------------------------------------------------------------------------------------------------*/

int const MOD = 1e9+7; 

ll inv (ll v) { 
    return (v <= 1 ? v : MOD - ((ll)(MOD / v) * inv(MOD % v) % MOD)); 
}

void sieve(vector<int>& v, int x) {
    vector<bool> s(x + 1);
    for (int i = 2; i <= x; i++) if (!s[i]) {
        v.push_back(i);
        for (int j = i+i; j <= x; j += i) s[j] = true; 
    }
}

void factorization(vector<ll>& v, ll x) {
    for (ll p = 2; p*p <= x; p++)
        while (x % p == 0) v.push_back(p), x /= p; 
    if (x > 1) v.push_back(x);
}

void get_divisors(vector<ll>& v, ll x) {
    for (ll i = 1; i*i <= x; i++)
        if (x % i == 0) {
            v.push_back(i);
            if (x/i != i) v.push_back(x/i);
        }
}

/*-------------------------------------------------------------------------------------------------*/
/*=======================================>> Strings <<=============================================*/
/*-------------------------------------------------------------------------------------------------*/

vector<int> z_function(string s) {
    int n = s.size();
    vector<int> z(n);
    int l = 0, r = 0;
    for(int i = 1; i < n; i++) {
        if(i < r) {
            z[i] = min(r - i, z[i - l]);
        }
        while(i + z[i] < n && s[z[i]] == s[i + z[i]]) {
            z[i]++;
        }
        if(i + z[i] > r) {
            l = i;
            r = i + z[i];
        }
    }
    return z;
}

/*-------------------------------------------------------------------------------------------------*/
/*=======================================>> Dynamic Programming <<=================================*/
/*-------------------------------------------------------------------------------------------------*/

struct subset_sum_problem
{
    int static const MAX_W = 40; 
    int static const MAX_N = 20; 
    int w[4] = {2, 4, 7, 8};
    int target = 14;

    bool solve()
    {
        bool dp[MAX_W + 1] = {0}; 
        dp[0] = true; 
        for (int i = 0; i < MAX_N; i++)
            for (int j = MAX_W; j >= w[i]; j--)
                dp[j] |= dp[j - w[i]];
        return dp[target];
    }

    bool solve_fast() 
    {
        bitset<MAX_W + 1> dp; 
        dp[0] = 1; 
        for (int i = 0; i < MAX_N; i++) dp |= (dp << w[i]);

        return dp[target];
    }
};

/*-------------------------------------------------------------------------------------------------*/
/*=======================================>> Data Structures <<=====================================*/
/*-------------------------------------------------------------------------------------------------*/

struct DSU {
    int n, comp; 
    vector<int> p, rank; 
    DSU(int n) { build(n); }
    void build(int m)
    {
        n = comp = m; 
        p = vector<int>(n + 1); 
        rank = vector<int>(n + 1);
        for (int i = 1; i <= n; i++) p[i] = i, rank[i] = 1;
    }
    void reset() { build(n); }
    int get(int u) { return (p[u] == u ? u : p[u] = get(p[u])); }
    void merge(int u, int v)
    {
        u = get(u); v = get(v); 
        if (u != v)
        {
            if (rank[u] < rank[v]) swap(u, v);
            p[v] = u; 
            rank[u] += rank[v];
            --comp;
        }
    }
};

template <typename T>
struct Fenwick {
    const int n;
    std::vector<T> a;
    Fenwick(int n) : n(n), a(n) {}
    void add(int x, T v) {
        for (int i = x + 1; i <= n; i += i & -i) {
            a[i - 1] += v;
        }
    }
    T sum(int x) { // [0, x)
        T ans = 0;
        for (int i = x; i > 0; i -= i & -i) {
            ans += a[i - 1];
        }
        return ans;
    }
    T rangeSum(int l, int r) { // [l, r)
        return sum(r) - sum(l);
    }
};

#include <ext/pb_ds/assoc_container.hpp>
using namespace __gnu_pbds;
template <class T>
using Tree =
    tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;

template <typename T>
struct binary_indexed_tree{
  int N;
  vector<T> BIT;
  binary_indexed_tree(int N): N(N), BIT(N + 1, 0){
  }
  void add(int i, T x){
    i++;
    while (i <= N){
      BIT[i] += x;
      i += i & -i;
    }
  }
  T sum(int i){
    T ans = 0;
    while (i > 0){
      ans += BIT[i];
      i -= i & -i;
    }
    return ans;
  }
  T sum(int L, int R){
    return sum(R) - sum(L);
  }
};

template <typename T>
struct SegTree {
    int N; 
    SegTree(int sz) { N = sz; }
    vector<T> tree(2*N);
    void combie(T i, T j) {
        return i + j; 
    }
    void build() { 
        for (int i = N - 1; i > 0; --i) t[i] combine(t[i<<1], t[i<<1|1]);
    }
    void modify(int p, T value) {  
        for (t[p += N] = value; p > 1; p >>= 1) t[p>>1] = combine(t[p], t[p^1]);
    }
    int query(int l, int r) { 
        T res = 0;
        for (l += N, r += N; l < r; l >>= 1, r >>= 1) {
            if (l&1) res = combine(res, t[l++]);
            if (r&1) res = combine(res, t[--r]);
        }
        return res;
    }
};

/*-------------------------------------------------------------------------------------------------*/
/*=======================================>> Graphs <<==============================================*/
/*-------------------------------------------------------------------------------------------------*/

bool is_bipartite(vector<vector<int>>& adj)
{
    int n = adj.size(); 
    vector<int> color;
    color = vector<int>(n + 1, -1);
    queue<pair<int, int>> q; // <v,color>
    q.push({1, 0});
    color[1] = 0; 
    pair<int, int> p; 
    while(!q.empty())
    {
        p = q.front(); q.pop(); 
        int v = p.first, c = p.second;
        for (auto ch : adj[v])
        {
            if (color[ch] == c) return false; 
            else if (color[ch] == -1)
            {
                color[ch] = c ? 0 : 1; 
                q.push({ch, color[ch]});
            }
        }
    }
    return true;
}

struct ShortestoPatho
{
    ll INF = 1e10; 
    int n = 1000, E = 1000, V = 1000; 

    struct Edge
    {
        int u, v, w; 
    };
    vector<Edge> edge;

    void digkstra(int source, vector<ll>& dist, vector<list<pair<int, int>>>& adj) 
    {   // nonnegative weights O((V + E) * logV)

        priority_queue<pair<ll, int>, vector<pair<ll, int>>, greater<pair<ll, int>>> que; 
        vector<bool> vis(n, false);
        dist[source] = 0; 
        que.push({0, source});
        for (int i = 0; i < n; i++) if (i != source) dist[i] = INF;

        pair<ll, int> p; 
        int u;
        ll d; 
        while (!que.empty())
        {
            p = que.top(); 
            u = p.second; 
            d = p.first;
            que.pop();
            vis[u] = true; 
            ll temp; 
            for (auto& [v, w] : adj[u])
            {
                if (vis[v]) continue; 
                temp = w + d; 
                if (temp < dist[v])
                {
                    dist[v] = temp; 
                    que.push({temp, v});
                }
            }
        }
    }

    void floydWarshall(vector<vector<int>>& dist) // dense graph, O(V^3)
    {
        for (int k = 0; k < n; k++) {
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (dist[i][j] > (dist[i][k] + dist[k][j]) && (dist[k][j] != INF && dist[i][k] != INF))
                        dist[i][j] = dist[i][k] + dist[k][j];
                }
            }
        }
    }

    void bellmanFord(int u, vector<int>& dist) // negative weights, O(E*V)
    {
        int V = n; // virtices
        int E = E; // edges

        for (int i = 0; i < V; i++)
            dist[i] = INT_MAX;

        dist[u] = 0;

        for (int i = 1; i <= V - 1; i++) {
            for (int j = 0; j < E; j++) {
            
                int u = edge[j].u;
                int v = edge[j].v;
                int w = edge[j].w;
                if (dist[u] != INT_MAX && dist[u] + w < dist[v])
                    dist[v] = dist[u] + w;
            }
        }

        for (int i = 0; i < E; i++) {
            int u = edge[i].u;
            int v = edge[i].v;
            int w = edge[i].w;
            if (dist[u] != INT_MAX && dist[u] + w < dist[v]) {
                printf("Graph contains negative w cycle");
                return;
            }
        }
    }
};
