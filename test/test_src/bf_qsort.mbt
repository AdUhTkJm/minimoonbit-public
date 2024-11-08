fn bf_qsort(arr: Array[Int], low: Int, high: Int) -> Unit {
    fn partition(arr: Array[Int], low: Int, high: Int,  pivot_index: Int) -> Int {
  fn swap(arr: Array[Int], fir: Int, sec: Int) -> Unit {
    let temp = arr[fir];
    arr[fir] = arr[sec];
    arr[sec] = temp;
    ()
  };
  if high <= low {
    if high == low {
      if arr[low] <= arr[pivot_index] {
        partition(arr, low + 1, high, pivot_index)
      } else {
        if arr[pivot_index] <= arr[high] {
          partition(arr, low, high - 1, pivot_index)
        } else {
          let _ = swap(arr, low, high);
          partition(arr, low + 1, high - 1, pivot_index)
        }
      }
    } else {
      let temp = arr[pivot_index];
      arr[pivot_index] = arr[high];
      arr[high] = temp;
      high
    }
  } else {
    if arr[low] <= arr[pivot_index] {
      partition(arr, low + 1, high, pivot_index)
    } else {
      if arr[pivot_index] <= arr[high] {
        partition(arr, low, high - 1, pivot_index)
      } else {
        let _ = swap(arr, low, high);
        partition(arr, low + 1, high - 1, pivot_index)
      }
    }
  }
};

  if low <= high {
    let new_pivot = partition(arr, low + 1, high, low);
    // let _ = print_int(new_pivot);
    let _ = bf_qsort(arr, low, new_pivot - 1);
    let _ = bf_qsort(arr, new_pivot + 1, high);
    ()
  }
};

fn main {
  let arr = Array::make(10, 0);
  arr[0] = 11;
  arr[1] = 3232;
  arr[2] = 54;
  arr[3] = 199999;
  arr[4] = 34;
  arr[5] = 555;
  arr[6] = 76;
  arr[7] = 2;
  arr[8] = 12345;
  arr[9] = 0;
  let _ = bf_qsort(arr, 0, 9);
  let _ = print_int(arr[0]);
  let _ = print_endline();
  let _ = print_int(arr[1]);
  let _ = print_endline();
  let _ = print_int(arr[2]);
  let _ = print_endline();
  let _ = print_int(arr[3]);
  let _ = print_endline();
  let _ = print_int(arr[4]);
  let _ = print_endline();
  let _ = print_int(arr[5]);
  let _ = print_endline();
  let _ = print_int(arr[6]);
  let _ = print_endline();
  let _ = print_int(arr[7]);
  let _ = print_endline();
  let _ = print_int(arr[8]);
  let _ = print_endline();
  let _ = print_int(arr[9]);
  let _ = print_endline();
  ()
};