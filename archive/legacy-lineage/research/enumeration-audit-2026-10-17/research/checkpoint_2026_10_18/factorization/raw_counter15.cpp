// Independent direct maximal-run deletion on labelled cell words.
// No grammar, partition witnesses, coefficient maps, or orbit canonicalization.
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

int main(int argc, char** argv) {
  const int q = argc > 1 ? std::atoi(argv[1]) : 3;
  const int nmax = argc > 2 ? std::atoi(argv[2]) : 13;
  if (q < 1 || q > 4 || nmax < 0 || nmax > 15) return 2;
  std::vector<std::uint64_t> power(nmax + 1, 1);
  std::vector<std::vector<std::uint8_t>> win(nmax + 1);
  for (int n = 1; n <= nmax; ++n) power[n] = q * power[n-1];
  win[0] = {1};
  std::cout << "{\"q\":" << q << ",\"n\":0,\"words\":1,\"winning\":1}\n";
  for (int n = 1; n <= nmax; ++n) {
    win[n].resize(power[n], 0);
    std::uint64_t count = 0;
    for (std::uint64_t code = 0; code < power[n]; ++code) {
      int cells[15];
      auto digits = code;
      for (int i = 0; i < n; ++i) {
        cells[i] = digits % q;
        digits /= q;
      }
      for (int i = 0; i < n;) {
        int j = i+1;
        while (j < n && cells[j] == cells[i]) ++j;
        if (j-i >= 2) {
          // Delete the ENTIRE maximal run [i,j), preserving cell order.
          const auto child = code % power[i] + (code / power[j]) * power[i];
          if (win[n-(j-i)][child]) {
            win[n][code] = 1;
            ++count;
            break;
          }
        }
        i = j;
      }
    }
    std::cout << "{\"q\":" << q << ",\"n\":" << n
              << ",\"words\":" << power[n] << ",\"winning\":" << count << "}\n";
  }
}
