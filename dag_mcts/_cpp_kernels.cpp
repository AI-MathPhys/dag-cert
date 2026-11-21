// Native C++17 confidence-maintenance and bandit kernels for DAG certification.
// Exposes an extern "C" entrypoint callable via Python ctypes with zero third-party
// dependencies. Measures pure C++ steady_clock nanoseconds (including cold index
// construction, rollout execution, confidence maintenance, queries, and RAII disposal).

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <limits>
#include <memory>
#include <queue>
#include <utility>
#include <vector>

namespace {

constexpr double kNegInf = -std::numeric_limits<double>::infinity();
constexpr double kPosInf = std::numeric_limits<double>::infinity();

struct WorkLedger {
  int64_t ops = 0;
};

// Deterministic SplitMix64 uniform [0, 1) draw for exact Python <-> C++ replay parity.
inline double splitmix_uniform01(uint64_t seed, int leaf, int obs_index) {
  uint64_t z = seed + 0x9e3779b97f4a7c15ULL * static_cast<uint64_t>(leaf + 1) +
               0xbf58476d1ce4e5b9ULL * static_cast<uint64_t>(obs_index);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  z = z ^ (z >> 31);
  return static_cast<double>(z >> 11) * (1.0 / 9007199254740992.0);
}

inline double draw_reward(uint64_t seed, int leaf, int obs_index, double mean, int reward_kind) {
  // reward_kind: 0 = deterministic, 1 = bernoulli(mean), 2 = uniform(mean - 0.01, mean + 0.01)
  if (reward_kind == 0) return mean;
  double u = splitmix_uniform01(seed, leaf, obs_index);
  if (reward_kind == 1) return (u < mean) ? 1.0 : 0.0;
  return std::clamp(mean + 0.01 * (2.0 * u - 1.0), 0.0, 1.0);
}

class MaxHeap {
 public:
  MaxHeap() = default;
  MaxHeap(const std::vector<double>& init_keys, WorkLedger* w)
      : keys(init_keys), ids(init_keys.size()), pos(init_keys.size()), work(w) {
    for (size_t i = 0; i < init_keys.size(); ++i) {
      ids[i] = static_cast<int>(i);
      pos[i] = static_cast<int>(i);
    }
    work->ops += static_cast<int64_t>(3 * init_keys.size());
    for (int i = static_cast<int>(ids.size()) / 2 - 1; i >= 0; --i) down(i);
  }

  inline bool better(int a, int b) const {
    work->ops += 1;
    return keys[a] > keys[b] || (keys[a] == keys[b] && a < b);
  }

  inline void swap_at(int i, int j) {
    int a = ids[i], b = ids[j];
    ids[i] = b;
    ids[j] = a;
    pos[a] = j;
    pos[b] = i;
    work->ops += 4;
  }

  void down(int i) {
    int n = static_cast<int>(ids.size());
    while (2 * i + 1 < n) {
      int ch = 2 * i + 1;
      if (ch + 1 < n && better(ids[ch + 1], ids[ch])) ++ch;
      if (!better(ids[ch], ids[i])) break;
      swap_at(i, ch);
      i = ch;
    }
  }

  void update(int item, double key) {
    double old = keys[item];
    keys[item] = key;
    work->ops += 1;
    int p = pos[item];
    if (key > old) {
      while (p > 0 && better(item, ids[(p - 1) / 2])) {
        int par = (p - 1) / 2;
        swap_at(p, par);
        p = par;
      }
    } else if (key < old) {
      down(p);
    }
  }

  inline int top() const { return ids[0]; }
  inline int second() const {
    if (ids.size() < 2) return -1;
    if (ids.size() == 2 || better(ids[1], ids[2])) return ids[1];
    return ids[2];
  }

  std::vector<double> keys;
  std::vector<int> ids;
  std::vector<int> pos;
  WorkLedger* work = nullptr;
};

class MinHeap {
 public:
  MinHeap() = default;
  MinHeap(const std::vector<double>& init_keys, WorkLedger* w)
      : keys(init_keys), ids(init_keys.size()), pos(init_keys.size()), work(w) {
    for (size_t i = 0; i < init_keys.size(); ++i) {
      ids[i] = static_cast<int>(i);
      pos[i] = static_cast<int>(i);
    }
    work->ops += static_cast<int64_t>(3 * init_keys.size());
    for (int i = static_cast<int>(ids.size()) / 2 - 1; i >= 0; --i) down(i);
  }

  inline bool better(int a, int b) const {
    work->ops += 1;
    return keys[a] < keys[b] || (keys[a] == keys[b] && a < b);
  }

  inline void swap_at(int i, int j) {
    int a = ids[i], b = ids[j];
    ids[i] = b;
    ids[j] = a;
    pos[a] = j;
    pos[b] = i;
    work->ops += 4;
  }

  void down(int i) {
    int n = static_cast<int>(ids.size());
    while (2 * i + 1 < n) {
      int ch = 2 * i + 1;
      if (ch + 1 < n && better(ids[ch + 1], ids[ch])) ++ch;
      if (!better(ids[ch], ids[i])) break;
      swap_at(i, ch);
      i = ch;
    }
  }

  void update(int item, double key) {
    double old = keys[item];
    keys[item] = key;
    work->ops += 1;
    int p = pos[item];
    if (key < old) {
      while (p > 0 && better(item, ids[(p - 1) / 2])) {
        int par = (p - 1) / 2;
        swap_at(p, par);
        p = par;
      }
    } else if (key > old) {
      down(p);
    }
  }

  inline int top() const { return ids[0]; }

  std::vector<double> keys;
  std::vector<int> ids;
  std::vector<int> pos;
  WorkLedger* work = nullptr;
};

struct GraphData {
  int num_nodes;
  int root;
  std::vector<std::vector<int>> children;
  std::vector<int> order;
  std::vector<int> rank;
  std::vector<int> leaves;
};

GraphData build_graph(int num_nodes, int root, const int* row_offsets, const int* col_indices) {
  GraphData g;
  g.num_nodes = num_nodes;
  g.root = root;
  g.children.resize(num_nodes);
  for (int u = 0; u < num_nodes; ++u) {
    int start = row_offsets[u], end = row_offsets[u + 1];
    g.children[u].assign(col_indices + start, col_indices + end);
    if (start == end) g.leaves.push_back(u);
  }
  // Compute topological order from root via DFS postorder reversal.
  std::vector<int> state(num_nodes, 0);
  std::vector<int> post;
  post.reserve(num_nodes);
  auto dfs = [&](auto& self, int u) -> void {
    state[u] = 1;
    for (int c : g.children[u]) {
      if (state[c] == 0) self(self, c);
    }
    post.push_back(u);
  };
  for (int u = 0; u < num_nodes; ++u) {
    if (state[u] == 0) dfs(dfs, u);
  }
  std::reverse(post.begin(), post.end());
  g.order = std::move(post);
  g.rank.assign(num_nodes, 0);
  for (int i = 0; i < num_nodes; ++i) g.rank[g.order[i]] = i;
  return g;
}

class EvidenceBox {
 public:
  EvidenceBox(const GraphData& g, double delta, int schedule, int eff_m, WorkLedger* w)
      : counts(g.num_nodes, 0),
        sums(g.num_nodes, 0.0),
        eb_sum_lam(schedule == 1 ? g.num_nodes : 0, 0.0),
        eb_sum_lam_x(schedule == 1 ? g.num_nodes : 0, 0.0),
        eb_sum_v_psi(schedule == 1 ? g.num_nodes : 0, 0.0),
        eb_var_acc(schedule == 1 ? g.num_nodes : 0, 0.25),
        lower(g.num_nodes, 0.0),
        upper(g.num_nodes, 1.0),
        sched(schedule),
        work(w) {
    int m = (eff_m > 0) ? eff_m : static_cast<int>(g.leaves.size());
    log_c = std::log((schedule == 1 ? 2.0 : 4.0) * m / delta);
    work->ops += static_cast<int64_t>((schedule == 1 ? 9 : 5) * g.num_nodes + 4);
  }

  bool observe(int leaf, double r, double* out_lo, double* out_hi) {
    int prev_n = counts[leaf];
    int n = prev_n + 1;
    counts[leaf] = n;
    double old_l = lower[leaf], old_u = upper[leaf];
    double lo = 0.0, hi = 1.0;
    if (sched == 1) {
      double hat_mu_prev = (0.5 + sums[leaf]) / static_cast<double>(n);
      double sig2_prev = eb_var_acc[leaf] / static_cast<double>(n);
      double lam = std::min(
          0.75, std::sqrt(2.0 * log_c / (sig2_prev * n * std::log(static_cast<double>(n) + 1.0))));
      double psi = -std::log(1.0 - lam) - lam;
      double v_n = (r - hat_mu_prev) * (r - hat_mu_prev);
      sums[leaf] += r;
      double hat_mu_curr = (0.5 + sums[leaf]) / (static_cast<double>(n) + 1.0);
      eb_var_acc[leaf] += (r - hat_mu_curr) * (r - hat_mu_curr);
      eb_sum_lam[leaf] += lam;
      eb_sum_lam_x[leaf] += lam * r;
      eb_sum_v_psi[leaf] += v_n * psi;
      double denom = eb_sum_lam[leaf];
      double center = eb_sum_lam_x[leaf] / denom;
      double width = (log_c + eb_sum_v_psi[leaf]) / denom;
      lo = std::max({old_l, center - width, 0.0});
      hi = std::min({old_u, center + width, 1.0});
      work->ops += 22;
    } else {
      sums[leaf] += r;
      double mean = sums[leaf] / n;
      double rad = std::sqrt((log_c + 2.0 * std::log(static_cast<double>(n))) / (2.0 * n));
      lo = std::max({old_l, mean - rad, 0.0});
      hi = std::min({old_u, mean + rad, 1.0});
      work->ops += 13;
    }
    lower[leaf] = lo;
    upper[leaf] = hi;
    if (lo > hi) {
      conflict = true;
      return false;
    }
    if (lo != old_l || hi != old_u) {
      strict_changes += 1;
      *out_lo = lo;
      *out_hi = hi;
      return true;
    }
    return false;
  }

  std::vector<int> counts;
  std::vector<double> sums;
  std::vector<double> eb_sum_lam, eb_sum_lam_x, eb_sum_v_psi, eb_var_acc;
  std::vector<double> lower;
  std::vector<double> upper;
  int sched = 0;
  double log_c = 0.0;
  int64_t strict_changes = 0;
  bool conflict = false;
  WorkLedger* work = nullptr;
};

// Graph-based confidence monitor supporting eager (0), protected-selective (1), and decision-selective (2).
class CppGraphBounds {
 public:
  CppGraphBounds(const GraphData& g, int mode_in, WorkLedger* w)
      : graph(g),
        mode(mode_in),
        lower(g.num_nodes, 0.0),
        upper(g.num_nodes, 1.0),
        live(g.num_nodes, 1),
        queued(g.num_nodes, 0),
        protected_node(g.num_nodes, 0),
        prunable_parent(g.num_nodes, 0),
        head(g.num_nodes, -1),
        indegree(g.num_nodes, 0),
        outgoing(g.num_nodes),
        low_heap(g.num_nodes),
        high_heap(g.num_nodes),
        min_upper(g.num_nodes),
        has_heaps(g.num_nodes, 0),
        has_min_heap(g.num_nodes, 0),
        work(w) {
    protected_node[g.root] = 1;
    if (mode != 2) {
      for (int c : g.children[g.root]) protected_node[c] = 1;
    }
    for (int v = 0; v < g.num_nodes; ++v) {
      prunable_parent[v] = (mode != 0 && !(mode == 1 && v == g.root)) ? 1 : 0;
      const auto& row = g.children[v];
      if (!row.empty()) {
        has_heaps[v] = 1;
        low_heap[v] = MaxHeap(std::vector<double>(row.size(), 0.0), w);
        high_heap[v] = MaxHeap(std::vector<double>(row.size(), 1.0), w);
        if (prunable_parent[v]) {
          has_min_heap[v] = 1;
          min_upper[v] = MinHeap(std::vector<double>(row.size(), 1.0), w);
        }
      }
    }
    w->ops += static_cast<int64_t>(14 * g.num_nodes + 8);
    for (int p = 0; p < g.num_nodes; ++p) {
      const auto& row = g.children[p];
      for (int a = 0; a < static_cast<int>(row.size()); ++a) {
        int c = row[a];
        int e = static_cast<int>(parent.size());
        parent.push_back(p);
        child.push_back(c);
        act_idx.push_back(a);
        prev_e.push_back(-1);
        next_e.push_back(head[c]);
        active.push_back(1);
        if (head[c] != -1) prev_e[head[c]] = e;
        head[c] = e;
        indegree[c] += 1;
        outgoing[p].push_back(e);
        w->ops += 12;
      }
    }
  }

  void unlink_edge(int e) {
    int c = child[e], bef = prev_e[e], aft = next_e[e];
    if (bef == -1)
      head[c] = aft;
    else
      next_e[bef] = aft;
    if (aft != -1) prev_e[aft] = bef;
    active[e] = 0;
    indegree[c] -= 1;
    retired += 1;
    work->ops += 8;
  }

  void release_node(int start) {
    if (mode == 0 || indegree[start] > 0 || protected_node[start]) return;
    std::vector<int> st = {start};
    while (!st.empty()) {
      int u = st.back();
      st.pop_back();
      work->ops += 2;
      if (!live[u] || protected_node[u] || indegree[u] > 0) continue;
      live[u] = 0;
      work->ops += 2;
      for (int e : outgoing[u]) {
        work->ops += 1;
        if (!active[e]) continue;
        int c = child[e];
        unlink_edge(e);
        if (indegree[c] == 0 && !protected_node[c]) st.push_back(c);
      }
    }
  }

  void cut_dominated(int p, double best_lo) {
    if (!has_min_heap[p]) return;
    auto& mh = min_upper[p];
    while (true) {
      work->ops += 2;
      int a = mh.top();
      if (mh.keys[a] >= best_lo) return;
      int e = outgoing[p][a];
      int c = child[e];
      unlink_edge(e);
      low_heap[p].update(a, kNegInf);
      high_heap[p].update(a, kNegInf);
      mh.update(a, kPosInf);
      release_node(c);
    }
  }

  bool record_bounds(int u, double lo, double hi) {
    work->ops += 2;
    if (lower[u] == lo && upper[u] == hi) return false;
    lower[u] = lo;
    upper[u] = hi;
    work->ops += 4;
    return true;
  }

  void publish(int leaf, double lo, double hi) {
    if (!record_bounds(leaf, lo, hi)) return;
    if (!live[leaf]) {
      work->ops += 1;
      return;
    }
    using PItem = std::pair<int, int>;
    std::priority_queue<PItem, std::vector<PItem>, std::greater<PItem>> pq;
    pq.emplace(-graph.rank[leaf], leaf);
    queued[leaf] = 1;
    std::vector<int> edge_buf;
    while (!pq.empty()) {
      auto [neg_r, u] = pq.top();
      (void)neg_r;
      pq.pop();
      queued[u] = 0;
      work->ops += 3;
      if (!live[u]) continue;
      edge_buf.clear();
      for (int e = head[u]; e != -1; e = next_e[e]) {
        edge_buf.push_back(e);
        work->ops += 2;
      }
      for (int e : edge_buf) {
        work->ops += 1;
        if (!active[e]) continue;
        int p = parent[e], a = act_idx[e];
        if (!live[p]) continue;
        messages += 1;
        work->ops += 6;
        if (low_heap[p].keys[a] != lower[u]) low_heap[p].update(a, lower[u]);
        if (high_heap[p].keys[a] != upper[u]) {
          high_heap[p].update(a, upper[u]);
          if (has_min_heap[p]) min_upper[p].update(a, upper[u]);
        }
        double nlo = low_heap[p].keys[low_heap[p].top()];
        if (has_min_heap[p]) cut_dominated(p, nlo);
        double nhi = high_heap[p].keys[high_heap[p].top()];
        work->ops += 3;
        if (record_bounds(p, nlo, nhi) && !queued[p]) {
          pq.emplace(-graph.rank[p], p);
          queued[p] = 1;
          work->ops += 3;
        }
      }
    }
  }

  std::pair<int, double> query_marginal() {
    const auto& row = graph.children[graph.root];
    work->ops += 2;
    if (row.empty()) return {-1, 0.0};
    if (row.size() == 1) return {0, 0.0};
    auto& lh = low_heap[graph.root];
    auto& hh = high_heap[graph.root];
    int best = lh.top();
    double best_lo = lh.keys[best];
    int top_u = hh.top();
    double rival_hi = kNegInf;
    if (top_u != best) {
      rival_hi = hh.keys[top_u];
      work->ops += 3;
    } else {
      int sec = hh.second();
      rival_hi = (sec >= 0) ? hh.keys[sec] : kNegInf;
      work->ops += 4;
    }
    return {best, std::max(0.0, rival_hi - best_lo)};
  }

  const GraphData& graph;
  int mode;
  std::vector<double> lower, upper;
  std::vector<uint8_t> live, queued, protected_node, prunable_parent;
  std::vector<int> head, indegree, parent, child, act_idx, prev_e, next_e;
  std::vector<uint8_t> active;
  std::vector<std::vector<int>> outgoing;
  std::vector<MaxHeap> low_heap, high_heap;
  std::vector<MinHeap> min_upper;
  std::vector<uint8_t> has_heaps, has_min_heap;
  int64_t messages = 0;
  int64_t retired = 0;
  WorkLedger* work = nullptr;
};

// Helper for ChargedDualCovers in C++17: compile positive & negative dyadic covers.
using Run = std::pair<int, int>;

std::vector<Run> merge_child_runs(const std::vector<const std::vector<Run>*>& lists, WorkLedger* w) {
  if (lists.empty()) return {};
  if (lists.size() == 1) {
    w->ops += 1;
    return *lists[0];
  }
  struct Item {
    int lo, hi, li, idx;
    bool operator>(const Item& o) const {
      if (lo != o.lo) return lo > o.lo;
      return hi > o.hi;
    }
  };
  std::priority_queue<Item, std::vector<Item>, std::greater<Item>> pq;
  for (int i = 0; i < static_cast<int>(lists.size()); ++i) {
    if (!lists[i]->empty()) {
      pq.push({(*lists[i])[0].first, (*lists[i])[0].second, i, 0});
      w->ops += 3;
    }
  }
  std::vector<Run> out;
  while (!pq.empty()) {
    auto cur = pq.top();
    pq.pop();
    w->ops += 3;
    if (!out.empty() && cur.lo <= out.back().second) {
      if (cur.hi > out.back().second) out.back().second = cur.hi;
    } else {
      out.emplace_back(cur.lo, cur.hi);
    }
    int nxt = cur.idx + 1;
    if (nxt < static_cast<int>(lists[cur.li]->size())) {
      pq.push({(*lists[cur.li])[nxt].first, (*lists[cur.li])[nxt].second, cur.li, nxt});
      w->ops += 3;
    }
  }
  return out;
}

std::vector<int> decompose_dyadic(const std::vector<Run>& runs, int seg_size, WorkLedger* w) {
  std::vector<int> blocks, left, right;
  for (auto [lo, hi] : runs) {
    int a = lo + seg_size, b = hi + seg_size;
    left.clear();
    right.clear();
    w->ops += 2;
    while (a < b) {
      w->ops += 4;
      if (a & 1) left.push_back(a++);
      if (b & 1) right.push_back(--b);
      a >>= 1;
      b >>= 1;
    }
    blocks.insert(blocks.end(), left.begin(), left.end());
    blocks.insert(blocks.end(), right.rbegin(), right.rend());
  }
  return blocks;
}

class CppDualCovers {
 public:
  CppDualCovers(const GraphData& g, WorkLedger* w) : graph(g), work(w) {
    int m = static_cast<int>(g.leaves.size());
    seg_size = 1;
    while (seg_size < m) seg_size <<= 1;
    const auto& root_ch = g.children[g.root];
    num_actions = static_cast<int>(root_ch.size());

    int64_t best_blocks = std::numeric_limits<int64_t>::max();
    for (int dfs_mode : {0, 1}) {
      std::vector<int> leaf_ord;
      leaf_ord.reserve(m);
      if (!dfs_mode) {
        leaf_ord = g.leaves;
      } else {
        std::vector<uint8_t> vis(g.num_nodes, 0);
        auto visit = [&](auto& self, int u) -> void {
          if (vis[u]) return;
          vis[u] = 1;
          if (g.children[u].empty()) {
            leaf_ord.push_back(u);
          } else {
            for (int c : g.children[u]) self(self, c);
          }
        };
        visit(visit, g.root);
        for (int z : g.leaves)
          if (!vis[z]) leaf_ord.push_back(z);
      }
      std::vector<int> rk(g.num_nodes, -1);
      for (int i = 0; i < m; ++i) rk[leaf_ord[i]] = i;
      w->ops += m;

      std::vector<std::vector<Run>> runs(g.num_nodes);
      for (int it = g.num_nodes - 1; it >= 0; --it) {
        int u = g.order[it];
        const auto& ch = g.children[u];
        w->ops += static_cast<int64_t>(ch.size());
        if (ch.empty()) {
          int j = rk[u];
          runs[u] = {{j, j + 1}};
        } else if (ch.size() == 1) {
          runs[u] = runs[ch[0]];
        } else {
          std::vector<const std::vector<Run>*> ptrs;
          ptrs.reserve(ch.size());
          for (int c : ch) ptrs.push_back(&runs[c]);
          runs[u] = merge_child_runs(ptrs, w);
        }
      }

      std::vector<std::vector<int>> pc(num_actions), nc(num_actions);
      int64_t tot = 0;
      for (int a = 0; a < num_actions; ++a) {
        const auto& pr = runs[root_ch[a]];
        std::vector<Run> nr;
        int prev = 0;
        for (auto [lo, hi] : pr) {
          if (prev < lo) nr.emplace_back(prev, lo);
          prev = hi;
          w->ops += 3;
        }
        if (prev < m) nr.emplace_back(prev, m);
        pc[a] = decompose_dyadic(pr, seg_size, w);
        nc[a] = decompose_dyadic(nr, seg_size, w);
        tot += static_cast<int64_t>(pc[a].size() + nc[a].size());
      }
      if (tot < best_blocks) {
        best_blocks = tot;
        rank_map = std::move(rk);
        pos_covers = std::move(pc);
        neg_covers = std::move(nc);
      }
    }

    low.assign(2 * seg_size, 0.0);
    high.assign(2 * seg_size, kNegInf);
    for (int j = 0; j < m; ++j) high[seg_size + j] = 1.0;
    for (int d = seg_size - 1; d >= 1; --d) {
      low[d] = std::max(low[2 * d], low[2 * d + 1]);
      high[d] = std::max(high[2 * d], high[2 * d + 1]);
    }
    w->ops += 6 * seg_size + m;

    pos_subs.resize(2 * seg_size);
    neg_subs.resize(2 * seg_size);
    pos_heaps.resize(num_actions);
    neg_heaps.resize(num_actions);
    has_neg.assign(num_actions, 0);
    std::vector<double> init_reg(num_actions, 0.0);

    for (int a = 0; a < num_actions; ++a) {
      std::vector<double> pk(pos_covers[a].size(), 0.0);
      for (int i = 0; i < static_cast<int>(pos_covers[a].size()); ++i) {
        int d = pos_covers[a][i];
        pos_subs[d].emplace_back(a, i);
        pk[i] = low[d];
      }
      pos_heaps[a] = MaxHeap(pk, w);
      if (!neg_covers[a].empty()) {
        has_neg[a] = 1;
        std::vector<double> nk(neg_covers[a].size(), 1.0);
        for (int i = 0; i < static_cast<int>(neg_covers[a].size()); ++i) {
          int d = neg_covers[a][i];
          neg_subs[d].emplace_back(a, i);
          nk[i] = high[d];
        }
        neg_heaps[a] = MaxHeap(nk, w);
        double la = pos_heaps[a].keys[pos_heaps[a].top()];
        double ua = neg_heaps[a].keys[neg_heaps[a].top()];
        init_reg[a] = std::max(0.0, ua - la);
      }
    }
    if (num_actions > 0) regret_heap = MinHeap(init_reg, w);
    touched_stamp.assign(num_actions, 0);
  }

  void publish(int leaf, double lo, double hi) {
    int d = seg_size + rank_map[leaf];
    step_epoch += 1;
    touched.clear();
    while (true) {
      work->ops += 2;
      bool lc = (lo != low[d]);
      bool hc = (hi != high[d]);
      if (!lc && !hc) break;
      if (lc) {
        low[d] = lo;
        work->ops += 1;
        for (auto [a, idx] : pos_subs[d]) {
          messages += 1;
          work->ops += 1;
          pos_heaps[a].update(idx, lo);
          if (touched_stamp[a] != step_epoch) {
            touched_stamp[a] = step_epoch;
            touched.push_back(a);
          }
        }
      }
      if (hc) {
        high[d] = hi;
        work->ops += 1;
        for (auto [a, idx] : neg_subs[d]) {
          messages += 1;
          work->ops += 1;
          neg_heaps[a].update(idx, hi);
          if (touched_stamp[a] != step_epoch) {
            touched_stamp[a] = step_epoch;
            touched.push_back(a);
          }
        }
      }
      if (d == 1) break;
      d >>= 1;
      lo = std::max(low[2 * d], low[2 * d + 1]);
      hi = std::max(high[2 * d], high[2 * d + 1]);
      work->ops += 6;
    }
    if (num_actions > 0) {
      for (int a : touched) {
        double reg = 0.0;
        if (has_neg[a]) {
          double la = pos_heaps[a].keys[pos_heaps[a].top()];
          double ua = neg_heaps[a].keys[neg_heaps[a].top()];
          work->ops += 2;
          reg = std::max(0.0, ua - la);
        }
        regret_heap.update(a, reg);
      }
    }
  }

  std::pair<int, double> query() {
    work->ops += 3;
    if (num_actions == 0) return {-1, 0.0};
    int best = regret_heap.top();
    return {best, regret_heap.keys[best]};
  }

  const GraphData& graph;
  int seg_size = 1;
  int num_actions = 0;
  std::vector<int> rank_map;
  std::vector<std::vector<int>> pos_covers, neg_covers;
  std::vector<double> low, high;
  std::vector<std::vector<std::pair<int, int>>> pos_subs, neg_subs;
  std::vector<MaxHeap> pos_heaps, neg_heaps;
  std::vector<uint8_t> has_neg;
  MinHeap regret_heap;
  std::vector<int> touched_stamp, touched;
  int step_epoch = 0;
  int64_t messages = 0;
  WorkLedger* work = nullptr;
};

// Direct-Graph Exact-Regret monitor in C++17 (no dyadic block compilation!).
class CppDirectGraphRegret {
 public:
  CppDirectGraphRegret(const GraphData& g, WorkLedger* w)
      : graph(g), bounds(g, 1, w), work(w) {
    int m = static_cast<int>(g.leaves.size());
    words = std::max(1, (m + 63) / 64);
    leaf_rank.assign(g.num_nodes, -1);
    for (int j = 0; j < m; ++j) leaf_rank[g.leaves[j]] = j;

    std::vector<uint64_t> masks(static_cast<size_t>(g.num_nodes) * words, 0ULL);
    for (int it = g.num_nodes - 1; it >= 0; --it) {
      int u = g.order[it];
      const auto& ch = g.children[u];
      if (ch.empty()) {
        int j = leaf_rank[u];
        masks[static_cast<size_t>(u) * words + (j >> 6)] = (1ULL << (j & 63));
        w->ops += 1;
      } else {
        uint64_t* dst = &masks[static_cast<size_t>(u) * words];
        for (int c : ch) {
          const uint64_t* src = &masks[static_cast<size_t>(c) * words];
          for (int b = 0; b < words; ++b) dst[b] |= src[b];
          w->ops += words;
        }
      }
    }
    const auto& row = g.children[g.root];
    num_actions = static_cast<int>(row.size());
    act_masks.resize(static_cast<size_t>(num_actions) * words);
    full_sup.assign(num_actions, 1);
    for (int a = 0; a < num_actions; ++a) {
      const uint64_t* src = &masks[static_cast<size_t>(row[a]) * words];
      uint64_t* dst = &act_masks[static_cast<size_t>(a) * words];
      for (int b = 0; b < words; ++b) {
        dst[b] = src[b];
        uint64_t want = (b + 1 < words || (m & 63) == 0) ? ~0ULL : ((1ULL << (m & 63)) - 1ULL);
        if (dst[b] != want) full_sup[a] = 0;
      }
    }
    term_upper = MaxHeap(std::vector<double>(m, 1.0), w);
  }

  void publish(int leaf, double lo, double hi) {
    bounds.publish(leaf, lo, hi);
    term_upper.update(leaf_rank[leaf], hi);
  }

  inline bool contains(int a, int j) const {
    return (act_masks[static_cast<size_t>(a) * words + (j >> 6)] >> (j & 63)) & 1ULL;
  }

  std::pair<int, double> query() {
    const auto& row = graph.children[graph.root];
    if (row.empty()) return {-1, 0.0};
    int top_j = term_upper.top();
    double top_u = term_upper.keys[top_j];
    int sec_j = term_upper.second();
    double sec_u = (sec_j >= 0) ? term_upper.keys[sec_j] : kNegInf;
    work->ops += 4;

    int best_a = 0;
    double best_reg = kPosInf;
    for (int a = 0; a < num_actions; ++a) {
      double la = bounds.lower[row[a]];
      work->ops += 1;
      double reg = 0.0;
      if (!full_sup[a]) {
        if (!contains(a, top_j)) {
          reg = std::max(0.0, top_u - la);
        } else if (sec_j >= 0 && !contains(a, sec_j)) {
          reg = std::max(0.0, sec_u - la);
        } else {
          double ua_out = kNegInf;
          for (int j = 0; j < static_cast<int>(term_upper.keys.size()); ++j) {
            work->ops += 2;
            if (!contains(a, j) && term_upper.keys[j] > ua_out) ua_out = term_upper.keys[j];
          }
          reg = std::max(0.0, ua_out - la);
        }
      }
      if (reg < best_reg) {
        best_reg = reg;
        best_a = a;
      }
    }
    return {best_a, best_reg};
  }

  const GraphData& graph;
  CppGraphBounds bounds;
  int words = 1;
  int num_actions = 0;
  std::vector<int> leaf_rank;
  std::vector<uint64_t> act_masks;
  std::vector<uint8_t> full_sup;
  MaxHeap term_upper;
  WorkLedger* work = nullptr;
};

}  // namespace

extern "C" {

struct CppRunResult {
  int64_t init_ns;
  int64_t total_ns;
  int64_t steps;
  int64_t work;
  int64_t messages;
  int64_t retired;
  int64_t strict_changes;
  int action;
  int certified;
};

// policy_kind: 0 = TA-UCT, 1 = Root-PUCT (unit lambda, fixed_first downstream)
// method_kind: 0 = graph-eager, 1 = protected-selective, 2 = decision-selective,
//              3 = dual-covers, 4 = direct-graph-regret
int run_certified_kernel(int num_nodes, int root, const int* row_offsets, const int* col_indices,
                         const double* leaf_means, int reward_kind, uint64_t seed,
                         int policy_kind, int method_kind, int schedule_kind,
                         double epsilon, double delta, double c_explore,
                         int q_cert, int eff_m, int cap, CppRunResult* out) {
  auto t_start = std::chrono::steady_clock::now();
  WorkLedger w;
  GraphData g = build_graph(num_nodes, root, row_offsets, col_indices);

  // Policy state
  std::vector<std::vector<int>> edge_counts(num_nodes);
  std::vector<std::vector<double>> edge_means(num_nodes);
  std::vector<int> visits(num_nodes, 0), untried(num_nodes, 0), leaf_obs(num_nodes, 0);
  for (int u = 0; u < num_nodes; ++u) {
    edge_counts[u].assign(g.children[u].size(), 0);
    edge_means[u].assign(g.children[u].size(), 0.0);
  }
  int root_deg = static_cast<int>(g.children[root].size());
  MaxHeap rec_heap(std::vector<double>(root_deg, kNegInf), &w);

  EvidenceBox ev(g, delta, schedule_kind, eff_m, &w);
  std::unique_ptr<CppGraphBounds> g_mon;
  std::unique_ptr<CppDualCovers> dual_mon;
  std::unique_ptr<CppDirectGraphRegret> dir_mon;

  if (method_kind <= 2) {
    g_mon = std::make_unique<CppGraphBounds>(g, method_kind, &w);
  } else if (method_kind == 3) {
    dual_mon = std::make_unique<CppDualCovers>(g, &w);
  } else {
    dir_mon = std::make_unique<CppDirectGraphRegret>(g, &w);
  }

  auto query_now = [&]() -> std::pair<int, double> {
    if (g_mon) return g_mon->query_marginal();
    if (dual_mon) return dual_mon->query();
    return dir_mon->query();
  };

  auto [q_act, q_gap] = query_now();
  bool cert = (!ev.conflict) && (q_gap <= epsilon);
  int rec_act = cert ? q_act : (root_deg > 0 ? rec_heap.top() : -1);

  auto t_init = std::chrono::steady_clock::now();
  int calls = 0;
  bool dirty = false;
  std::vector<std::pair<int, int>> path_edges;
  path_edges.reserve(64);

  while (!cert && !ev.conflict && calls < cap) {
    int u = root;
    path_edges.clear();
    while (!g.children[u].empty()) {
      int deg = static_cast<int>(g.children[u].size());
      int chosen = 0;
      if (policy_kind == 0) {
        if (untried[u] < deg) {
          chosen = untried[u]++;
          w.ops += 1;
        } else {
          double x = std::sqrt(std::log1p(static_cast<double>(visits[u])));
          double best_s = kNegInf;
          for (int a = 0; a < deg; ++a) {
            w.ops += 2;
            double slope = c_explore / std::sqrt(static_cast<double>(edge_counts[u][a]));
            double s = edge_means[u][a] + slope * x;
            if (s > best_s) {
              best_s = s;
              chosen = a;
            }
          }
        }
      } else {
        if (u == root) {
          if (calls < deg) {
            chosen = calls;
            w.ops += 1;
          } else {
            double st = std::sqrt(static_cast<double>(calls));
            double best_s = kNegInf;
            for (int a = 0; a < deg; ++a) {
              w.ops += 2;
              double s = edge_means[u][a] + st / static_cast<double>(1 + edge_counts[u][a]);
              if (s > best_s) {
                best_s = s;
                chosen = a;
              }
            }
          }
        } else {
          chosen = 0;
          w.ops += 1;
        }
      }
      path_edges.emplace_back(u, chosen);
      u = g.children[u][chosen];
    }

    int obs_k = ++leaf_obs[u];
    double reward = draw_reward(seed, u, obs_k, leaf_means[u], reward_kind);
    calls += 1;
    for (int i = static_cast<int>(path_edges.size()) - 1; i >= 0; --i) {
      auto [par, act] = path_edges[i];
      visits[par] += 1;
      int cnt = ++edge_counts[par][act];
      edge_means[par][act] += (reward - edge_means[par][act]) / static_cast<double>(cnt);
      w.ops += 4;
    }
    if (!path_edges.empty()) {
      int a0 = path_edges[0].second;
      rec_heap.update(a0, edge_means[root][a0]);
    }

    double lo = 0.0, hi = 1.0;
    if (ev.observe(u, reward, &lo, &hi)) {
      dirty = true;
      if (g_mon)
        g_mon->publish(u, lo, hi);
      else if (dual_mon)
        dual_mon->publish(u, lo, hi);
      else
        dir_mon->publish(u, lo, hi);
    }

    if (dirty && (calls % q_cert == 0)) {
      dirty = false;
      std::tie(q_act, q_gap) = query_now();
      if (!ev.conflict && q_gap <= epsilon) {
        cert = true;
        rec_act = q_act;
      }
    }
    if (!cert) rec_act = (root_deg > 0) ? rec_heap.top() : -1;
  }

  int64_t msgs = g_mon ? g_mon->messages : (dual_mon ? dual_mon->messages : dir_mon->bounds.messages);
  int64_t ret = g_mon ? g_mon->retired : (dir_mon ? dir_mon->bounds.retired : 0);

  // Explicitly reset heap/monitor allocations inside steady_clock timer so disposal is timed!
  g_mon.reset();
  dual_mon.reset();
  dir_mon.reset();
  auto t_end = std::chrono::steady_clock::now();

  out->init_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(t_init - t_start).count();
  out->total_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(t_end - t_start).count();
  out->steps = calls;
  out->work = w.ops;
  out->messages = msgs;
  out->retired = ret;
  out->strict_changes = ev.strict_changes;
  out->action = rec_act;
  out->certified = cert ? 1 : 0;
  return 0;
}

}  // extern "C"
