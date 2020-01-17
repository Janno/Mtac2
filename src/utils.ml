module NEList = struct
  let fold_right_i f i l a =
    let rec go i = function
      | [] -> failwith "list empty"
      | x :: [] -> f i x (a, None)
      | x :: l ->
          let a, b = go (i + 1) l in
          f i x (a, Some b)
    in go i l

  let fold_right f = fold_right_i (fun i -> f) 0

  let fold_left_i f i a l =
    let rec go i a = function
      | [] -> failwith "list empty"
      | x :: [] -> f i a x
      | x :: l ->
          let a = f i a x in
          go (i+1) a l
    in go i a l
end
