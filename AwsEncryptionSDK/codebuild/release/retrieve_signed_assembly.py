from signing_lib import retrieve_signed_assembly, parse_args


if __name__ == '__main__':
    args = parse_args()
    retrieve_signed_assembly(args)
