#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <dirent.h>
#include <sys/stat.h>
#include <errno.h>

static void fail_with_message(const char *message) {
    fprintf(stderr, "Error: %s\n", message);
    exit(EXIT_FAILURE);
}

static void fail_with_perror(const char *message) {
    perror(message);
    exit(EXIT_FAILURE);
}

static int compare_u64(const void *a, const void *b) {
    uint64_t val_a = *(const uint64_t *)a;
    uint64_t val_b = *(const uint64_t *)b;
    if (val_a < val_b) return -1;
    if (val_a > val_b) return 1;
    return 0;
}

static void process_file(const char *dir_path, const char *filename, FILE *results_fp) {
    char *line = NULL;
    uint64_t *numbers = NULL;
    FILE *input_fp = NULL;
    FILE *output_fp = NULL;
    int status = EXIT_FAILURE;

    char *endptr;
    long n_long = strtol(filename, &endptr, 10);
    if (endptr == filename || *endptr != '.' || n_long <= 0) {
        fail_with_message("Invalid filename format");
    }
    size_t n = (size_t)n_long;

    char input_path[FILENAME_MAX];
    snprintf(input_path, sizeof(input_path), "%s/%s", dir_path, filename);

    input_fp = fopen(input_path, "r");
    if (!input_fp) {
        fail_with_perror("Failed to open input file");
    }

    if (n <= 100000) {
        char output_path[FILENAME_MAX];
        snprintf(output_path, sizeof(output_path), "./data/output/%s", filename);
        output_fp = fopen(output_path, "a");
        if (!output_fp) {
            fail_with_perror("Failed to open output file");
        }
    }

    numbers = malloc(n * sizeof(uint64_t));
    if (!numbers) {
        fail_with_perror("Failed to allocate memory for numbers array");
    }

    size_t line_cap = 0;
    char datagen_method[256];

    while (getline(&line, &line_cap, input_fp) != -1) {
        line[strcspn(line, "\r\n")] = 0;
        char *rest = line;
        char *token;

        token = strsep(&rest, ",");
        if (!token) { fail_with_message("Malformed line: missing id"); }
        uint64_t id = strtoull(token, &endptr, 10);
        if (*endptr) { fail_with_message("Malformed line: invalid id"); }

        token = strsep(&rest, ",");
        if (!token) { fail_with_message("Malformed line: missing create_time"); }

        token = strsep(&rest, ",");
        if (!token) { fail_with_message("Malformed line: missing datagen_method"); }
        strncpy(datagen_method, token, sizeof(datagen_method) - 1);
        datagen_method[sizeof(datagen_method) - 1] = '\0';

        for (size_t i = 0; i < n; ++i) {
            token = strsep(&rest, ",");
            if (!token) { fail_with_message("Malformed line: insufficient number columns"); }
            numbers[i] = strtoull(token, &endptr, 10);
            if (*endptr) { fail_with_message("Malformed line: invalid number in array"); }
        }

        if (strsep(&rest, ",")) { fail_with_message("Malformed line: too many columns"); }

        struct timespec start_ts, end_ts;
        char time_buf[32];
        time_t now = time(NULL);
        strftime(time_buf, sizeof(time_buf), "%Y-%m-%dT%H:%M:%SZ", gmtime(&now));

        clock_gettime(CLOCK_MONOTONIC, &start_ts);
        qsort(numbers, n, sizeof(uint64_t), compare_u64);
        clock_gettime(CLOCK_MONOTONIC, &end_ts);

        long sort_time_ms = (end_ts.tv_sec - start_ts.tv_sec) * 1000 +
                              (end_ts.tv_nsec - start_ts.tv_nsec) / 1000000;

        if (output_fp) {
            fprintf(output_fp, "%llu,%s,%s", (unsigned long long)id, time_buf, datagen_method);
            for (size_t i = 0; i < n; ++i) {
                fprintf(output_fp, ",%llu", (unsigned long long)numbers[i]);
            }
            fprintf(output_fp, "\n");
        }

        fprintf(results_fp, "%llu,%s,%s,c_qsort,%ld\n",
                (unsigned long long)id, time_buf, datagen_method, sort_time_ms);
    }

    if (ferror(input_fp)) {
        fail_with_perror("Error reading from input file");
    }

    status = EXIT_SUCCESS;

cleanup:
    free(line);
    free(numbers);
    if (input_fp) fclose(input_fp);
    if (output_fp) fclose(output_fp);
    if (status == EXIT_FAILURE) exit(EXIT_FAILURE);
}

int main(void) {
    const char *input_dir_path = "./data/input";
    const char *output_dir_path = "./data/output";
    const char *results_path = "./data/results.csv";

    struct stat st;
    if (stat(input_dir_path, &st) != 0 || !S_ISDIR(st.st_mode)) {
        fail_with_message("./data/input is not a valid directory");
    }

    if (stat(output_dir_path, &st) != 0) {
        if (mkdir(output_dir_path, 0755) != 0 && errno != EEXIST) {
            fail_with_perror("Failed to create ./data/output directory");
        }
    }

    FILE *results_fp = fopen(results_path, "a");
    if (!results_fp) {
        fail_with_perror("Failed to open ./data/results.csv");
    }

    DIR *d = opendir(input_dir_path);
    if (!d) {
        fclose(results_fp);
        fail_with_perror("Failed to open ./data/input directory");
    }

    struct dirent *dir;
    while ((dir = readdir(d)) != NULL) {
        if (dir->d_type == DT_REG) {
            const char *filename = dir->d_name;
            const char *dot = strrchr(filename, '.');
            if (dot && strcmp(dot, ".csv") == 0) {
                process_file(input_dir_path, filename, results_fp);
            }
        }
    }

    closedir(d);
    fclose(results_fp);

    return EXIT_SUCCESS;
}
