CXX = clang++
CXXFLAGS = -std=c++20 -Wall -Wextra -Werror -g
OBJS = level.o kernel.o printer.o main.o

kernel: $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $(OBJS)

level.o: level.cpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

kernel.o: kernel.cpp kernel.hpp expression.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

printer.o: printer.cpp printer.hpp expression.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

main.o: main.cpp expression.hpp kernel.hpp printer.hpp level.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f kernel $(OBJS)

.PHONY: clean
