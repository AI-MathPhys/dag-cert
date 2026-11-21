// Fast native -O3 C++17 SameGame playout & reference-mean evaluator.
// Matches `paper/samegame_gate.py` (`Moves`, `finish`, `Game`, `GameOracle`) rules
// identically (column-major flood-fill, gravity + empty-column collapse, (n-2)^2
// move rewards, +1000 board-clear bonus, -sum max(n_c-2,0)^2 residual penalty).

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <vector>

namespace {

constexpr int kMaxCols = 16;
constexpr int kMaxRows = 16;
constexpr int kMaxColors = 8;
constexpr int kMaxMoves = 128;

struct Board {
  int ncols;
  uint8_t col_len[kMaxCols];
  uint8_t cells[kMaxCols][kMaxRows];
};

inline uint64_t splitmix64_next(uint64_t& state) {
  uint64_t z = (state += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}

inline int finish_bonus(const Board& b) {
  if (b.ncols == 0) return 1000;
  int counts[kMaxColors] = {0};
  int max_c = 0;
  for (int x = 0; x < b.ncols; ++x) {
    for (int y = 0; y < b.col_len[x]; ++y) {
      int c = b.cells[x][y];
      if (c >= 0 && c < kMaxColors) {
        counts[c]++;
        if (c > max_c) max_c = c;
      }
    }
  }
  int pen = 0;
  for (int c = 0; c <= max_c; ++c) {
    if (counts[c] > 2) {
      int d = counts[c] - 2;
      pen -= d * d;
    }
  }
  return pen;
}

// Single uniform-random legal SameGame playout from `start_board` to termination.
double playout_once(Board b, int base_points, int B_offset, double inv_scale, uint64_t rng_state) {
  int score = base_points;
  uint8_t vis[kMaxCols][kMaxRows];
  int comp_id[kMaxCols][kMaxRows];
  int move_id[kMaxMoves];
  int move_size[kMaxMoves];
  int stack_x[kMaxCols * kMaxRows];
  int stack_y[kMaxCols * kMaxRows];

  while (b.ncols > 0) {
    for (int x = 0; x < b.ncols; ++x) {
      std::memset(vis[x], 0, b.col_len[x]);
    }
    int num_moves = 0;
    int cid = 0;

    for (int x = 0; x < b.ncols; ++x) {
      int clen = b.col_len[x];
      for (int y = 0; y < clen; ++y) {
        if (vis[x][y]) continue;
        uint8_t color = b.cells[x][y];
        vis[x][y] = 1;
        cid++;
        comp_id[x][y] = cid;
        int sp = 0;
        stack_x[sp] = x;
        stack_y[sp] = y;
        sp++;
        int gsize = 1;

        while (sp > 0) {
          sp--;
          int i = stack_x[sp];
          int j = stack_y[sp];
          // 4-neighbors matching `((i-1,j),(i+1,j),(i,j-1),(i,j+1))`
          const int nx[4] = {i - 1, i + 1, i, i};
          const int ny[4] = {j, j, j - 1, j + 1};
          for (int d = 0; d < 4; ++d) {
            int a = nx[d];
            int r = ny[d];
            if (a >= 0 && a < b.ncols && r >= 0 && r < b.col_len[a] &&
                !vis[a][r] && b.cells[a][r] == color) {
              vis[a][r] = 1;
              comp_id[a][r] = cid;
              stack_x[sp] = a;
              stack_y[sp] = r;
              sp++;
              gsize++;
            }
          }
        }
        if (gsize >= 2) {
          move_id[num_moves] = cid;
          move_size[num_moves] = gsize;
          num_moves++;
        }
      }
    }

    if (num_moves == 0) break;

    int pick = (num_moves == 1)
                   ? 0
                   : static_cast<int>(splitmix64_next(rng_state) % static_cast<uint64_t>(num_moves));
    int target_cid = move_id[pick];
    int dm = move_size[pick] - 2;
    score += dm * dm;

    // Remove `target_cid` cells and collapse empty columns.
    int new_ncols = 0;
    for (int x = 0; x < b.ncols; ++x) {
      int write_y = 0;
      int clen = b.col_len[x];
      for (int y = 0; y < clen; ++y) {
        if (comp_id[x][y] != target_cid) {
          b.cells[new_ncols][write_y++] = b.cells[x][y];
        }
      }
      if (write_y > 0) {
        b.col_len[new_ncols] = static_cast<uint8_t>(write_y);
        new_ncols++;
      }
    }
    b.ncols = new_ncols;
  }

  int total_raw = score + finish_bonus(b) + B_offset;
  double val = static_cast<double>(total_raw) * inv_scale;
  if (val < 0.0) val = 0.0;
  if (val > 1.0) val = 1.0;
  return val;
}

Board unpack_board(const uint8_t* flat_cells, const uint8_t* col_lens, int ncols) {
  Board b;
  b.ncols = ncols;
  int pos = 0;
  for (int x = 0; x < ncols; ++x) {
    uint8_t len = col_lens[x];
    b.col_len[x] = len;
    for (int y = 0; y < len; ++y) {
      b.cells[x][y] = flat_cells[pos++];
    }
  }
  return b;
}

struct RegisteredGame {
  std::vector<Board> leaves;
  std::vector<int> base_points;
  int B_offset = 0;
  double inv_scale = 1.0;
};

std::vector<RegisteredGame>& registry() {
  static std::vector<RegisteredGame> reg;
  return reg;
}

}  // namespace

extern "C" {

int cpp_samegame_register_game(
    int num_leaves,
    const int* leaf_cell_offsets,
    const uint8_t* all_flat_cells,
    const int* leaf_col_offsets,
    const uint8_t* all_col_lens,
    const int* leaf_ncols,
    const int* leaf_points,
    int B_offset,
    double inv_scale) {
  RegisteredGame rg;
  rg.leaves.resize(num_leaves);
  rg.base_points.assign(leaf_points, leaf_points + num_leaves);
  rg.B_offset = B_offset;
  rg.inv_scale = inv_scale;
  for (int li = 0; li < num_leaves; ++li) {
    rg.leaves[li] = unpack_board(
        all_flat_cells + leaf_cell_offsets[li],
        all_col_lens + leaf_col_offsets[li],
        leaf_ncols[li]);
  }
  auto& reg = registry();
  int handle = static_cast<int>(reg.size());
  reg.push_back(std::move(rg));
  return handle;
}

double cpp_samegame_sample_fast(
    int handle,
    int leaf_rank,
    int leaf_orig_id,
    int obs_index,
    uint64_t seed) {
  const auto& rg = registry()[handle];
  uint64_t rng = seed ^ (0x9E3779B97F4A7C15ULL * static_cast<uint64_t>(leaf_orig_id + 1)) ^
                 (0xBF58476D1CE4E5B9ULL * static_cast<uint64_t>(obs_index));
  splitmix64_next(rng);
  return playout_once(rg.leaves[leaf_rank], rg.base_points[leaf_rank], rg.B_offset, rg.inv_scale, rng);
}

double cpp_samegame_sample_one(
    const uint8_t* flat_cells,
    const uint8_t* col_lens,
    int ncols,
    int base_points,
    int B_offset,
    double inv_scale,
    uint64_t seed,
    int leaf_id,
    int obs_index) {
  Board b = unpack_board(flat_cells, col_lens, ncols);
  uint64_t rng = seed ^ (0x9E3779B97F4A7C15ULL * static_cast<uint64_t>(leaf_id + 1)) ^
                 (0xBF58476D1CE4E5B9ULL * static_cast<uint64_t>(obs_index));
  splitmix64_next(rng);
  return playout_once(b, base_points, B_offset, inv_scale, rng);
}

void cpp_samegame_batch_means(
    int num_leaves,
    const int* leaf_cell_offsets,
    const uint8_t* all_flat_cells,
    const int* leaf_col_offsets,
    const uint8_t* all_col_lens,
    const int* leaf_ncols,
    const int* leaf_points,
    int B_offset,
    double inv_scale,
    int num_samples_per_leaf,
    uint64_t base_seed,
    double* out_means) {
  for (int li = 0; li < num_leaves; ++li) {
    Board b = unpack_board(
        all_flat_cells + leaf_cell_offsets[li],
        all_col_lens + leaf_col_offsets[li],
        leaf_ncols[li]);
    int pts = leaf_points[li];
    double sum = 0.0;
    for (int k = 1; k <= num_samples_per_leaf; ++k) {
      uint64_t rng = base_seed ^ (0x9E3779B97F4A7C15ULL * static_cast<uint64_t>(li + 1)) ^
                     (0xBF58476D1CE4E5B9ULL * static_cast<uint64_t>(k));
      splitmix64_next(rng);
      sum += playout_once(b, pts, B_offset, inv_scale, rng);
    }
    out_means[li] = sum / static_cast<double>(num_samples_per_leaf);
  }
}

}  // extern "C"
