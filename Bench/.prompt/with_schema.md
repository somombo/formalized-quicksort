# Prompt: High-Performance CSV Sorting Task

## Role and Goal

You are a `[Programming-Language-Name]` expert. Your goal is to write a high-performance, single-threaded, and idiomatic program in that language. The program iterates through a directory of CSV files. For each file, it must stream the contents line-by-line, sort a large array of numbers from each line, and write the sorted data and performance metrics to two separate output files.

---

## I/O Specifications

The program must process every file in the `data/input/` directory. The name of each input file, `[N].csv`, indicates the number of integers (`N`) on each line of that file. For each input file `data/input/[N].csv`, the program will generate a corresponding `data/output/[N].csv`.

### Input Files: `data/input/[N].csv`

*   **Format**: A CSV file with no header row.
*   **Reading Strategy**: Must be read using a streaming, line-by-line approach to minimize memory usage.
*   **Line Schema**: Each line contains 6 metadata fields followed by `N` unsigned 64-bit integers, where `N` is derived from the input filename.

| Column Name      | Data Type | Description                                             |
| :--------------- | :-------- | :------------------------------------------------------ |
| `id`             | `UInt64`  | A unique identifier for the row.                        |
| `create_time`    | `String`  | **To be ignored.** A new timestamp will be generated.   |
| `unique_frac`    | `Float64` | Metadata float value.                                   |
| `swap_ratio`     | `Float64` | Metadata float value.                                   |
| `reverse`        | `Boolean` | Informational metadata only. **Does not control sort order.** |
| `size`           | `USize`   | Metadata size value (always `N`).                       |
| `a[0]`...`a[N-1]`| `UInt64`  | The array of `N` numbers to be sorted.                  |

---

### Output File 1: `data/output/[N].csv`

*   **Mode**: Create if not exists, append if it does.
*   **Format**: A CSV file with no header row.
*   **Line Schema**: Contains the original metadata (with the **newly generated `create_time`**) followed by the sorted array of `N` numbers.

---

### Output File 2: `data/results.csv`

*   **Mode**: Create if not exists, append if it does. This file is a single, shared log for all processed input files.
*   **Format**: A CSV file with no header row.
*   **Line Schema**:

| Column Name          | Data Type | Description                                                      |
| :------------------- | :-------- | :--------------------------------------------------------------- |
| `id`                 | `UInt64`  | Copied from the input line.                                      |
| `create_time`        | `String`  | The **newly generated** timestamp in `YYYY-MM-DDTHH:MM:SSZ`. |
| `unique_frac`        | `Float64` | Copied from the input line.                                      |
| `swap_ratio`         | `Float64` | Copied from the input line.                                      |
| `reverse`            | `Boolean` | Copied from the input line.                                      |
| `size`               | `USize`   | Copied from the input line (value is `N`).                       |
| `sort_time`          | `Integer` | The time taken for the sort, in **milliseconds**.                |
| `sortfn_description` | `String`  | A hardcoded string: `programming_language_name_sort`.                            |

---

## Core Processing Logic

The program should first find all files in the `data/input` directory. For each file `data/input/[N].csv` found, it should perform the following steps:

1.  **Parse `N`**: Extract the integer `N` from the filename.
2.  **Process Lines**: For each line read from `data/input/[N].csv`, perform the following steps sequentially:
    1.  **Parse**:
        *   Read the 6 metadata fields. The value of the second field (`create_time`) is discarded.
        *   Read the subsequent `N` values into an in-memory array of `UInt64`. The array's capacity must be pre-allocated to exactly `N`.

    2.  **Timestamp and Sort**:
        *   Capture the current system time to be used as the new `create_time`.
        *   Start a high-precision timer.
        *   Sort the `UInt64` array in **ascending order** (so the `reverse` field from input *does not* determine sort order).
        *   Stop the timer and record the duration in milliseconds.

    3.  **Write and Flush**:
        *   Convert the `create_time` timestamp captured in the previous step into a string with the format `YYYY-MM-DDTHH:MM:SSZ`.
        *   Append a single line to `data/output/[N].csv` containing the metadata (using the new timestamp) followed by the sorted array.
        *   Append a single line to `data/results.csv` containing the metadata (using the new timestamp), the sort duration, and the hardcoded function name.

---

## Constraints and Requirements

*   **Dependencies**: Use **only** the language's standard library. No third-party packages are permitted.
*   **Concurrency**: The solution must be strictly single-threaded.
*   **Error Handling**: If any line in an input file is malformed (e.g., incorrect column count, non-numeric data), or if `data/input` is not a directory, or if a filename in `data/input` does not parse to an integer, the program must **immediately terminate** with a non-zero exit code.
*   **Code Style**: The code must be simple, clean, idiomatic, safe (have no undefined behavior or memory leaks)and I/O operations must follow best practices to guarantee data integrity.
*   **No Data Generation**: Assume the `data/input/[N].csv` files already exist (do not write a seperate data generator script). The `data/input` directory is guaranteed to exist (do nothing if it is empty).
*   **No Logging**: Do not include any logging or debug output in the final code.
*   **No Comments**: Do not include any comments in the final code.
*   **No build scripts**: Do not include any build or project configuration files in the final code.