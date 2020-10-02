def read_input(file: str = "in.txt") -> List[str]:
    """ Read the input from a file. """
    file_read = open(file, "r").read()
    filtered_file = filter(None, file_read.split("\n"))
    return list(filtered_file)


if __name__ == "__main__":
    if len(sys.argv) <= 1:
        print(f"Correct sytax is: python3 {sys.argv[0]} [FILE.txt] [SET]")
        print(f"For example: python3 {sys.argv[0]} my_input.txt A,D,E")
        sys.exit(1)
    inp = read_input(sys.argv[1])
    my_set = set(sys.argv[2].split(","))
    fd_obj = FDs(str_to_fds(inp))

    if not fd_obj.set_is_valid(my_set):
        print(f"ERROR: {my_set} is not a subset of {fd_obj.alphabet}")
        sys.exit(1)

    fd_obj.print_cover_set(my_set)
    fd_obj.print_all_minimal_keys()
    fd_obj.print_determinants(my_set)
    fd_obj.print_canonical()
    fd_obj.to_bcnf()
    fd_obj.to_3nf()
