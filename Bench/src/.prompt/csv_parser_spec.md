# Prompt: High-Performance CSV Sorting Task

## Role and Goal

You are a `[Programming-Language-Name]` expert. Your goal is to write a high-performance, single-threaded, and idiomatic program in that language. The program iterates through a directory of CSV files. For each file, it must stream the contents line-by-line, sort an array of numbers from each line, write the sorted data (if it is small enough) to one file and performance metrics to another.

---

## I/O Specifications

The program must process every file in the `data/input/` directory. The name of each input file, `{size}.csv`, indicates the number of integers (`size`) on each line of that file. For each input file `data/input/{size}.csv` for which `size` is no greater than `100,000`, the program will generate a corresponding `data/output/{size}.csv`.

### Input Files: `data/input/{size}.csv`

*   **Format**: A CSV file with no header row.
*   **Reading Strategy**: Must be read using a streaming, line-by-line approach to minimize memory usage.
*   **Line Schema**: Each line contains 3 metadata fields followed by `size` unsigned 64-bit integers, where `size` is derived from the input filename.

| Column Name      | Data Type | Description                                             |
| :--------------- | :-------- | :------------------------------------------------------ |
| `id`             | `UInt64`  | Metadata: describing a unique identifier for the row.                        |
| `create_time`    | `String`  | Metadata: **To be ignored.** A new timestamp will be generated.   |
| `datagen_method`   | `String`  | Metadata: string value describing how array was generated.   |
| `a[0]`...`a[size-1]`| `UInt64`  | The array of `size` numbers to be sorted.                  |

---

### Output Files: `data/output/{size}.csv` (for `size` ≤ 100,000)

*   **Mode**: Create if not exists, append if it does.
*   **Format**: A CSV file with no header row.
*   **Line Schema**: Contains the original metadata (with the **newly generated `create_time`**) followed by the sorted array of `size` numbers.

---

### Result Log Files: `data/results.csv` (for all `size`s)

*   **Mode**: Create if not exists, append if it does. This file is a single, shared log for all processed input files.
*   **Format**: A CSV file with no header row.
*   **Line Schema**:

| Column Name          | Data Type | Description                                                      |
| :------------------- | :-------- | :--------------------------------------------------------------- |
| `id`                 | `UInt64`  | Copied from the input line.                                      |
| `create_time`        | `String`  | The **newly generated** timestamp in format `YYYY-MM-DDTHH:MM:SSZ`. |
| `datagen_method`   | `String`  | Copied from the input line.   |
| `sort_method` | `String`  | A string value describing the method used to sort the array. For example: hardcode something like `programming-language-name__sort-function-name__machine-name`. |
| `sort_time`          | `Integer` | The time taken for the sort, in **milliseconds**.                |

---

## Core Processing Logic

The program should first find all files in the `data/input` directory. For each file `data/input/{size}.csv` found, it should perform the following steps:

1.  **Parse `size`**: Extract the integer `size` from the filename. Size should be of type `USize` if that type makes sense and is available in the programming language.
2.  **Process Lines**: For each line read from `data/input/{size}.csv`, perform the following steps sequentially:
    1.  **Parse**:
        *   Read the 3 metadata fields. The value of the second field (`create_time`) is discarded.
        *   Read the subsequent `size` values into an in-memory array of `UInt64`. The array's capacity must be pre-allocated to exactly `size`.

    2.  **Timestamp and Sort**:
        *   Capture the current system time to be used as the new `create_time`.
        *   Start a high-precision timer.
        *   Sort the `UInt64` array in **ascending order**.
        *   Stop the timer and record the duration in milliseconds.

    3.  **Write and Flush**:
        *   Convert the `create_time` timestamp captured in the previous step into a string with the format `YYYY-MM-DDTHH:MM:SSZ`.
        *   If `size` is not more than 100,000 then append a single line to `data/output/{size}.csv` containing the metadata (using the new timestamp) followed by the sorted array.
        *   Append a single line to `data/results.csv` containing the metadata (using the new timestamp), the sort duration, and the hardcoded function name.

---

## Constraints and Requirements

*   **Dependencies**: Use **only** the language's standard library. No third-party packages are permitted.
*   **Concurrency**: The solution must be strictly single-threaded.
*   **Error Handling**: If any line in an input file is malformed (e.g., incorrect column count, non-numeric data), or if `data/input` is not a directory, or if a filename in `data/input` does not parse to an integer, the program must **immediately terminate** with a non-zero exit code.
*   **Code Style**: The code must be simple, clean, idiomatic, safe (have no undefined behavior or memory leaks)and I/O operations must follow best practices to guarantee data integrity.
*   **No Data Generation**: Assume the `data/input/{size}.csv` files already exist (do not write a seperate data generator script). The `data/input` directory is guaranteed to exist (do nothing if it is empty).
*   **No Logging**: Do not include any logging or debug output in the final code.
*   **No Comments**: Do not include any comments in the final code.
*   **No build scripts**: Do not include any build or project configuration files in the final code.