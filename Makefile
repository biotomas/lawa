all:
	g++ -O3 lawa-main.cpp lawa.cpp -std=c++11 -o lawa
clean:
	rm lawa
