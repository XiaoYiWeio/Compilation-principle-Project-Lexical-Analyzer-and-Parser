#include <iostream>
#include <fstream>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <iomanip>
#include "Lex_Analysis.h"
#include "Grammar_Analysis.h"

using namespace std;

int main()
{
	
    //词法分析部分
    initKeyMapping();
    initOperMapping();
    initLimitMapping();
    initNode();
    scanner();
    //语法分析部分
    initGrammer();
    First();
    Follow();
    Select();
    MTable();
    Analysis();

    return 0;
}
