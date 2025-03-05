#!/usr/bin/env python3

import sys
import os
import argparse

def combine_files_with_headers(input_files, output_file, input_encoding='utf-8', output_encoding='utf-8'):
    """
    Combines the content of multiple input files into a single output file,
    preceding each file's content with a header indicating its path.

    Args:
        input_files (list): A list of file paths to combine.
        output_file (str): The path to the output file.
        input_encoding (str, optional): Encoding to use for reading input files. Defaults to 'utf-8'.
        output_encoding (str, optional): Encoding to use for writing the output file. Defaults to 'utf-8'.

    Raises:
        FileNotFoundError: If an input file does not exist.
        PermissionError: If there are permission issues reading input or writing output.
        UnicodeDecodeError: If input files cannot be decoded with the specified encoding.
        IOError: For general input/output errors.
        Exception: For unexpected errors during file processing.
    """

    try:
        with open(output_file, 'w', encoding=output_encoding) as outfile:
            for input_file in input_files:
                try:
                    if not os.path.isfile(input_file):
                        print(f"Warning: Input path '{input_file}' is not a file, skipping.", file=sys.stderr)
                        continue

                    with open(input_file, 'r', encoding=input_encoding) as infile:
                        outfile.write(f"=== {input_file} ===\n")
                        outfile.write(infile.read())
                        outfile.write("\n\n")
                    print(f"Processed file: {input_file}")

                except FileNotFoundError as e:
                    print(f"Error: Input file not found: {input_file}: {e}", file=sys.stderr)
                    raise # Re-raise to be caught at a higher level if needed
                except PermissionError as e:
                    print(f"Error: Permission denied to read: {input_file}: {e}", file=sys.stderr)
                    raise
                except UnicodeDecodeError as e:
                    print(f"Error: Could not decode file '{input_file}' using {input_encoding} encoding: {input_file}: {e}. Consider specifying the correct encoding.", file=sys.stderr)
                    raise
                except IOError as e:
                    print(f"Error reading file '{input_file}': {e}", file=sys.stderr)
                    raise
                except Exception as e:
                    print(f"Error processing file '{input_file}': {e}", file=sys.stderr)
                    raise

        print(f"Successfully combined files into: {output_file} (encoding: {output_encoding})")

    except PermissionError as e:
        print(f"Error: Permission denied to write to output file: {output_file}: {e}", file=sys.stderr)
        raise
    except IOError as e:
        print(f"Error writing to output file '{output_file}': {e}", file=sys.stderr)
        raise
    except Exception as e:
        print(f"An unexpected error occurred while writing to output: {e}", file=sys.stderr)
        raise


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Combine multiple files into one with headers and encoding options.")
    parser.add_argument("input_files", nargs='+', help="List of input file paths to combine.")
    parser.add_argument("-o", "--output", dest="output_file", default="combined_files.txt",
                        help="Path to the output file (default: combined_files.txt)")
    parser.add_argument("--input-encoding", dest="input_encoding", default='utf-8',
                        help="Encoding for input files (default: utf-8)")
    parser.add_argument("--output-encoding", dest="output_encoding", default='utf-8',
                        help="Encoding for output file (default: utf-8)")

    args = parser.parse_args()

    try:
        combine_files_with_headers(args.input_files, args.output_file, args.input_encoding, args.output_encoding)
    except (FileNotFoundError, PermissionError, UnicodeDecodeError, IOError, Exception) as e: # Catch re-raised exceptions for cleaner exit if needed
        print(f"\nScript execution failed due to an error. See error messages above.", file=sys.stderr)
        sys.exit(1) # Exit with non-zero code to indicate failure
