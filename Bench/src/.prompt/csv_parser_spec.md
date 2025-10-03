# Prompt

Write a program in idiomatic [Programming-Language-Name] that efficiently parses and sorts large arrays of numbers from a CSV file.

## Core Requirements

1.  **Functionality**: The program must read a CSV file where each line contains **exactly one million** comma-separated, non-negative integers. For each line, it must sequentially perform the following steps:
    a. Parse the line into an in-memory array of integers. Since the size is known beforehand, pre-allocate the array's capacity to 1,000,000 for efficiency.
    b. Start a timer (should be able to time in milliseconds).
    c. Sort the array in place using an efficient standard library sort.
    d. Stop the timer.
    e. Print the time taken for that specific sort operation to standard output, in milliseconds.
    f. Write the newly sorted vector as a single comma-separated line to an output CSV file, appending a newline character after each line.

2.  **Performance & Memory**: The input file can be very large. The program **must not** load the entire file into memory. It should process the file line-by-line using an idiomatic streaming approach to maintain a low memory footprint.

3.  **File Handling**: Use the hardcoded filename `input.csv` for reading and `sorted_output.csv` for writing. The program should create `sorted_output.csv` if it doesn't exist, or append to it if it does.

4.  **Error Handling**: If any line in the input file is malformed (e.g., contains non-numeric data, is empty, or parsing fails for any reason), the program **should immediately panic** and terminate.

## Constraints

* **No External Crates**: Do not use any third-party dependencies. All code must use at most, only the language's idomatic standard library.
* **No Concurrency**: The solution must be single-threaded.
* **No Comments**: Do not include any comments in the final code.
* **No Data Generation**: Assume the `input.csv` file already exists.