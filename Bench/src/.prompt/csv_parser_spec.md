# Prompt: High-Performance CSV Sorting Task

## Role & Goal
You are a `[Programming-Language-Name]` expert. Your goal is to write a high-performance, single-threaded, and idiomatic program that performs a CSV sorting task according to the specifications below.

---

## Task Details

### Overview
The program must iterate through all files in the `data/input/` directory. For each file, it will stream the contents line-by-line, sort an array of numbers from each line, and write the sorted data and performance metrics to separate output files.

### Processing Logic
For each file named `data/input/{size}.csv`:
1.  **Parse `size`**: Extract the integer `size` from the filename. This indicates the number of integers per line.
2.  **Stream Lines**: For each line in the input file:
    a. **Parse Data**: Read the 3 metadata fields and the subsequent `size` `UInt64` numbers into an array pre-allocated to capacity `size`.
    b. **Timestamp**: Generate a new timestamp.
    c. **Sort & Time**: Start a high-precision timer, sort the `UInt64` array in ascending order, stop the timer, and record the duration in milliseconds.
    d. **Write Output**: If `size <= 100,000`, append a record to `data/output/{size}.csv`.
    e. **Write Log**: Append a performance metric record to the shared `data/results.csv` file.

---

### I/O Schemas
All CSV files are headerless. Output files should be created if non-existent or appended to if they exist.

**1. Input: `data/input/{size}.csv`**
| Field | Type | Note |
|---|---|---|
| `id` | `UInt64` | Keep for output. |
| `create_time` | `String` | **Discard** and replace with a new timestamp. |
| `datagen_method` | `String` | Keep for output. |
| `array...` | `UInt64[]` | An array of `size` integers to be sorted. |

**2. Output: `data/output/{size}.csv`** (Written only if `size <= 100,000`)
| Field | Type | Note |
|---|---|---|
| `id` | `UInt64` | From input. |
| `create_time` | `String` | **New** timestamp, format: `YYYY-MM-DDTHH:MM:SSZ`. |
| `datagen_method` | `String` | From input. |
| `sorted_array...` | `UInt64[]` | The sorted array of `size` integers. |

**3. Log: `data/results.csv`** (Written for every line processed)
| Field | Type | Note |
|---|---|---|
| `id` | `UInt64` | From input. |
| `create_time` | `String` | **New** timestamp, format: `YYYY-MM-DDTHH:MM:SSZ`. |
| `datagen_method` | `String` | From input. |
| `sort_method` | `String` | Hardcoded string, e.g., `lang__sort-func__machine`. |
| `sort_time_ms` | `Integer` | Sort duration in **milliseconds**. |

---

## Requirements & Constraints
* **Dependencies**: Use **only** the language's standard library. No third-party packages.
* **Concurrency**: The solution must be strictly **single-threaded**.
* **Error Handling**: The program must **terminate immediately** with a non-zero exit code if any line is malformed, a filename does not parse to an integer, or `data/input` is not a directory.
* **Code Style**: The code must be clean, idiomatic, and memory-safe. I/O operations must be robust to ensure data integrity.
* **Environment**:
    * Assume `data/input/{size}.csv` files and the `data/input` directory already exist.
    * Do not include any data generation script, build files, logging, or comments in the final code.