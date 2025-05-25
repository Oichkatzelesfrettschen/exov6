posix_tests = files('../../src-uland/posix_file_test.c',
                    '../../src-uland/posix_signal_test.c',
                    '../../src-uland/posix_pipe_test.c',
                    '../../src-uland/user/libos_posix_extra_test.c')
foreach src : posix_tests
  exe_name = src.stem()
  executable(exe_name, src,
             include_directories: include_directories('../../src-headers'),
             install: false)
endforeach
