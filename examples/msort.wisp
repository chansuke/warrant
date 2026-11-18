defn merge [a : (Vec i64) b : (Vec i64)] -> (Vec i64)
  :effects []
  :requires (sorted? a) (sorted? b)
  :ensures (sorted? result) (perm? result (concat a b))
  if (empty? a) b
    if (empty? b) a
      if (<= (get a 0) (get b 0))
        cons (get a 0) (merge (rest a) b)
        cons (get b 0) (merge a (rest b))

defn msort [xs : (Vec i64)] -> (Vec i64)
  :effects []
  :ensures (sorted? result) (perm? result xs)
  let [n (len xs)]
    if (<= n 1) xs
      let [h (/ n 2)] : merge (msort (slice xs 0 h)) (msort (slice xs h n))

defn gen [n : i64 seed : i64] -> (Vec i64)
  :effects []
  map (fn [i] (mod (+ (* i 7919) seed) 10007)) (range n)

defn main [] -> (Vec i64)
  :effects []
  :budget (wall-ms 500)
  slice (msort (gen 2000 42)) 0 10
