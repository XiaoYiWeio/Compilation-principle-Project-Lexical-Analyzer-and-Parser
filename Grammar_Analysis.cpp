#include <iostream>  
#include <stdio.h>  
#include <stdlib.h>  
#include <string.h>  
#include <conio.h>  
#include <fstream>  
#include <vector>  
#include <conio.h>  
#include "Lex_Analysis.h"  
#include "Grammar_Analysis.h"  
#include<iomanip>


using namespace std;  
  
#define Max_Proc 500  
#define Max_Length 500  
  
#define Max_NonTer 60  
#define Max_Ter 60  
#define Max_Length2 100  
  
int pd_num = 0;  
//proc的维数都是从1开始的  
#define MAX_PD 500
int pd_word[MAX_PD][MAX_PD];//产生式的数组，里边存储了终结符或者非终结符对应的编号  
int first[MAX_PD][MAX_PD];  // first集
int follow[MAX_PD][MAX_PD]; // follow集
int select[MAX_PD][MAX_PD]; // select集
int M[Max_NonTer][Max_Ter][Max_Length2];  //预测分析表
  
int connectFirst[Max_Length];//将某些First集结合起来的集合  
  
  
int firstVisit[Max_Proc];//记录某非终结符的First集是否已经求过  
int followVisit[Max_Proc];//记录某非终结符的Follow集是否已经求过  
  
int Empty[Max_Proc];//可推出空的非终结符的编号  
int emptyRecu[Max_Proc];//在求可推出空的非终结符的编号集时使用的防治递归的集合  
int followRecu[Max_Proc];//在求Follow集时使用的防治递归的集合  
  
//extern的部分代表可能出现的终结符和其编号  
extern vector<pair<const char *,int> > keyMap;  
extern vector<pair<const char *,int> > operMap;  
extern vector<pair<const char *,int> > limitMap;  
  
extern NormalNode * normalHead;//首结点  
  
fstream resultfile;  
  
vector<pair<const char *,int> > NotEndDic;			//非终结符映射表			,不可重复的  
vector<pair<const char *,int> > EndDic;				//终结符映射表				,不可重复的  
vector<pair<const char *,int> > SpecialDic;			//文法中的特殊符号映射表	，包括-> | $(空)  
  
  
void initSpecialMapping()  
{  
    SpecialDic.clear();  
    SpecialDic.push_back(make_pair("->",GRAMMAR_ARROW));  
    SpecialDic.push_back(make_pair("|",GRAMMAR_OR));  
    SpecialDic.push_back(make_pair("$",GRAMMAR_NULL));  
    SpecialDic.push_back(make_pair("#",GRAMMAR_SPECIAL));  
  
}  
const char * searchMapping(int num)  
{  
    //标志符  
    if(num == IDENTIFER)  
    {  
        return "ID";  
    }  
    //处理文法中的特殊符号  
    for(int i = 0; i<SpecialDic.size(); i++)  
    {  
        if(SpecialDic[i].second == num)  
        {  
            return SpecialDic[i].first;  
        }  
    }  
    //处理非终结符  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        if(NotEndDic[i].second == num)  
        {  
            return NotEndDic[i].first;  
        }  
    }  
    //处理终结符  
    for(int i=0; i<EndDic.size(); i++)  
    {  
        if(EndDic[i].second == num)  
        {  
            return EndDic[i].first;  
        }  
    }  
  
}  
  
//动态生成非终结符，在基点的基础上，确保不和终结符冲突  
int Gene_NotEnd(char *word)  
{  
    int i = 0;  
    int dynamicNum;  
    for(i=0; i<NotEndDic.size(); i++)  
    {  
        if(strcmp(word,NotEndDic[i].first) == 0)  
        {  
            return NotEndDic[i].second;  
        }  
    }  
    if(i == NotEndDic.size())  
    {  
        if(i == 0)  
        {  
            dynamicNum = GRAMMAR_BASE;  
            NotEndDic.push_back(make_pair(word,dynamicNum));  
        }  
        else  
        {  
            dynamicNum = NotEndDic[NotEndDic.size()-1].second + 1;  
            NotEndDic.push_back(make_pair(word,dynamicNum));  
        }  
    }  
    return dynamicNum;  
}  
//判断某个标号是不是非终结符的标号,1代表是，0代表否  
int _NotEnd(int n)  
{  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        if(NotEndDic[i].second == n)  
        {  
            return 1;  
        }  
    }  
    return 0;  
}  
//判断某个标号是不是终结符的标号，1代表是，0代表否  
int inTer(int n)  
{  
    for(int i=0; i<EndDic.size(); i++)  
    {  
        if(EndDic[i].second == n)  
        {  
            return 1;  
        }  
    }  
    return 0;  
}  
//判断某个标号在不在此时的Empty集中，1代表是，0代表否  
int inEmpty(int n)  
{  
    //当前Empty集的长度  
    int emptyLength = 0;  
    for(emptyLength = 0;; emptyLength++)  
    {  
        if(Empty[emptyLength] == -1)  
        {  
            break;  
        }  
    }  
    for(int i = 0; i<emptyLength; i++)  
    {  
        if(Empty[i] == n)  
        {  
            return 1;  
        }  
    }  
    return 0;  
  
}  
//判断某个标号在不在此时的emptyRecu集中，1代表是，0代表否  
int inEmptyRecu(int n)  
{  
    //当前Empty集的长度  
    int emptyLength = 0;  
    for(emptyLength = 0;; emptyLength++)  
    {  
        if(emptyRecu[emptyLength] == -1)  
        {  
            break;  
        }  
    }  
    for(int i = 0; i<emptyLength; i++)  
    {  
        if(emptyRecu[i] == n)  
        {  
            return 1;  
        }  
    }  
    return 0;  
}  
//判断某个标号在不在此时的followRecu集中，1代表是，0代表否  
int inFollowRecu(int n)  
{  
    int followLength = 0;  
    for(followLength = 0;; followLength++)  
    {  
        if(followRecu[followLength] == -1)  
        {  
            break;  
        }  
    }  
    for(int i = 0; i<followLength; i++)  
    {  
        if(followRecu[i] == n)  
        {  
            return 1;  
        }  
    }  
    return 0;  
}  
  
//判断某个标号是不是在产生式的右边  
int inProcRight(int n,int * p)  
{  
    //注意这里默认是从3开始  
    for(int i=3;; i++)  
    {  
        if(p[i] == -1)  
        {  
            break;  
        }  
        if(p[i] == n)  
        {  
            return 1;  
        }  
    }  
    return 0;  
}  
  
int seekCodeNum(char * word)  
{  
    //处理文法中的特殊符号  
    for(int i = 0; i<SpecialDic.size(); i++)  
    {  
        if(strcmp(word,SpecialDic[i].first) == 0)  
        {  
            return SpecialDic[i].second;  
        }  
    }  
    //先搜索终结符映射表中有没有此终结符  
    for(int i=0; i<EndDic.size(); i++)  
    {  
        if(strcmp(word,EndDic[i].first) == 0)  
        {  
            return EndDic[i].second;  
        }  
    }  
    for(int i = 0; i<keyMap.size(); i++)  
    {  
        if(strcmp(word,keyMap[i].first) == 0)  
        {  
            EndDic.push_back(make_pair(word,keyMap[i].second));  
            return keyMap[i].second;  
        }  
    }  
  
    for(int i = 0; i<operMap.size(); i++)  
    {  
        if(strcmp(word,operMap[i].first) == 0)  
        {  
            EndDic.push_back(make_pair(word,operMap[i].second));  
            return operMap[i].second;  
        }  
    }  
  
    for(int i = 0; i<limitMap.size(); i++)  
    {  
        if(strcmp(word,limitMap[i].first) == 0)  
        {  
            EndDic.push_back(make_pair(word,limitMap[i].second));  
            return limitMap[i].second;  
        }  
    }  
  
    if(strcmp(word,"ID")==0)  
    {  
        //处理标志符  
        EndDic.push_back(make_pair(word,IDENTIFER));  
        return IDENTIFER;  
    }  
    else  
    {  
        //处理关键字、运算符、限界符表，即非终结符  
        return Gene_NotEnd(word);  
    }  
}  
//分割" | "文法  
void splitProc(int p[][Max_Length],int &line,int orNum)  
{  
    if(p[line][1] == -1 || orNum == 0)  
    {  
        return;  
    }  
    int head = p[line][1];  
    int push = p[line][2];  
    int length = 0;  
    int right,left;  
    int lineTrue = line + orNum;  
    for(length = 3;;length++)  
    {  
        if(p[line][length] == -1)  
        {  
            break;  
        }  
    }  
    length--;  
    for(left = length,right = length;left>=2;)  
    {  
        if(p[line][left] == GRAMMAR_OR || left == 2)  
        {  
            p[line + orNum][1] = head;  
            p[line + orNum][2] = push;  
            for(int i=left+1;i<=right;i++)  
            {  
                p[line+orNum][i-left+2] = p[line][i];  
            }  
            p[line+orNum][right-left+3] = -1;  
            right = left = left-1;  
            orNum--;  
        }  
        else  
        {  
            left--;  
        }  
    }  
    line = lineTrue;  
}  
void initGrammer()  
{  
    FILE * infile;  
    char ch;  
    char array[30];  
    char * word;  
    int i;  
    int codeNum;  
    int line = 1;  
    int count = 0;  
    int orNum = 0;  
    infile = fopen("wenfa.txt","r");  
    if(!infile)  
    {  
        printf("文法打开失败！\n");  
        return;  
    }  
    initSpecialMapping();  
    NotEndDic.clear();  
    EndDic.clear();  
  
    memset(pd_word,-1,sizeof(pd_word));  
    memset(first,-1,sizeof(first));  
    memset(follow,-1,sizeof(follow));  
    memset(select,-1,sizeof(select));  
  
    memset(connectFirst,-1,sizeof(connectFirst));  
  
    memset(firstVisit,0,sizeof(firstVisit));	//非终结符的first集还未求过  
    memset(followVisit,0,sizeof(followVisit));	//非终结符的follow集还未求过  
  
    memset(Empty,-1,sizeof(Empty));  
    memset(emptyRecu,-1,sizeof(emptyRecu));  
    memset(followRecu,-1,sizeof(followRecu));  
  
    memset(M,-1,sizeof(M));  
  
    ch = fgetc(infile);  
    i = 0;  
    while(ch!=EOF)  
    {  
        i = 0;  
        while(ch == ' ' || ch == '\t')  
        {  
            ch = fgetc(infile);  
        }  
        while(ch!=' ' && ch!= '\n' && ch!=EOF)  
        {  
            array[i++] = ch;  
            ch = fgetc(infile);  
        }  
        while(ch == ' ' || ch == '\t')  
        {  
            ch = fgetc(infile);  
        }  
        word = new char[i+1];  
        memcpy(word,array,i);  
        word[i] = '\0';  
        codeNum = 0;  
        codeNum = seekCodeNum(word);  
        if(codeNum!=0)  
        {  
            count++;  
            if(codeNum == GRAMMAR_OR)  
            {  
                orNum++;  
            }  
            pd_word[line][count] = codeNum;  
  
        }  
												//原本需要回退一个字符，由于是冗余字符，不回退  
        if(ch == '\n')  
        {  
            splitProc(pd_word,line,orNum);			//将" | "文法进行拆分  
            count = 0;  
            orNum = 0;  
            line++;  
            ch = fgetc(infile);  
        }  
    }  
    pd_num = line - 1;  
	
    printf("\n终结符如下:\n\n");  
    for(int i=0; i<EndDic.size(); i++)  
    {  
        cout<<setw(20)<<EndDic[i].first; 
		if ((i+1) % 4 == 0)
			cout << endl;
    }  
    printf("\n");  
    printf("\n非终结符如下:\n\n");  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        cout<<setw(20)<<NotEndDic[i].first; 
		if ((i+1) % 4 == 0)
			cout << endl;
    }  
    printf("\n");  
}  
//将s集合合并至d集合中，type = 1代表包括空（$）,type = 2代表不包括空  
void merge(int *d,int *s,int type)  
{  
    int flag = 0;  
    for(int i = 0;; i++)  
    {  
        flag = 0;  
        if(s[i] == -1)  
        {  
            break;  
        }  
        int j = 0;  
        for(j = 0;; j++)  
        {  
            if(d[j] == -1)  
            {  
                break;  
            }  
            if(d[j] == s[i])  
            {  
                flag = 1;  
                break;  
            }  
        }  
        if(flag == 1)  
        {  
            continue;  
        }  
        if(type == 1)  
        {  
            d[j] = s[i];  
        }  
        else  
        {  
            if(s[i] != GRAMMAR_NULL)  
            {  
                d[j] = s[i];  
            }  
        }  
        d[j + 1] = -1;  
    }  
}  
  
void nullSet(int currentNum)  
{  
    int temp[2];  
    for(int j = 1; j<=pd_num; j++)  
    {  
        //如果右边的第一个是该字符，并且长度只有1  
        if(pd_word[j][3] == currentNum && pd_word[j][4] == -1)  
        {  
            temp[0] = pd_word[j][1];  
            temp[1] = -1;  
            merge(Empty,temp,1);  
            nullSet(pd_word[j][1]);  
        }  
    }  
}  
//判断该非终结符是否能推出空，但终结符也可能传入，但没关系  
int reduNull(int currentNon)  
{  
    int temp[2];  
    int result = 1;  
    int mark = 0;  
    temp[0] = currentNon;  
    temp[1] = -1;  
    merge(emptyRecu,temp,1);//先将此符号并入防递归集合中  
    if(inEmpty(currentNon) == 1)  
    {  
        return 1;  
    }  
  
    for(int j = 1; j<=pd_num; j++)  
    {  
        if(pd_word[j][1] == currentNon)  
        {  
            int rightLength = 0;  
            //先求出右部的长度  
            for(rightLength = 3;; rightLength++)  
            {  
                if(pd_word[j][rightLength] == -1)  
                {  
                    break;  
                }  
            }  
            rightLength--;  
            //如果长度为1，并且已经求过  
            if(rightLength - 2 == 1 && inEmpty(pd_word[j][rightLength]))  
            {  
                return 1;  
            }  
            //如果长度为1，并且是终结符  
            else if(rightLength -2 == 1 && inTer(pd_word[j][rightLength]))  
            {  
                return 0;  
            }  
            //如果长度超过了2  
            else  
            {  
                for(int k=3; k<=rightLength; k++)  
                {  
                    if(inEmptyRecu(pd_word[j][k]))  
                    {  
                        mark = 1;  
                    }  
                }  
                if(mark == 1)  
                {  
                    continue;  
                }  
                else  
                {  
                    for(int k=3; k<=rightLength; k++)  
                    {  
                        result*= reduNull(pd_word[j][k]);  
                        temp[0] = pd_word[j][k];  
                        temp[1] = -1;  
                        merge(emptyRecu,temp,1);//先将此符号并入防递归集合中  
                    }  
                }  
            }  
            if(result == 0)  
            {  
                continue;  
            }  
            else if(result == 1)  
            {  
                return 1;  
            }  
        }  
    }  
    return 0;  
}  
  
//求first集，传入的参数是在非终结符集合中的序号  
void Gene_first(int i)  
{  
    int k = 0;  
    int currentNon = NotEndDic[i].second;	//当前的非终结符标号  
											//依次遍历全部产生式  
    for(int j = 1; j<=pd_num; j++)			//j代表第几个产生式  
    {  
        //找到该非终结符的产生式  
        if(currentNon == pd_word[j][1])		//注意从1开始  
        {  
											//当右边的第一个是终结符或者空的时候  
            if(inTer(pd_word[j][3]) == 1 || pd_word[j][3] == GRAMMAR_NULL)  
            {  
											//并入当前非终结符的first集中  
                int temp[2];  
                temp[0] = pd_word[j][3];  
                temp[1] = -1;				//其实是模拟字符串操作的手段  
                merge(first[i],temp,1);  
            }  
											//当右边的第一个是非终结符的时候  
            else if(_NotEnd(pd_word[j][3]) == 1)  
            {  
											//记录下右边第一个非终结符在非终结符映射表中的位置  
                for(k=0;; k++)  
                {  
                    if(NotEndDic[k].second == pd_word[j][3])  
                    {  
                        break;  
                    }  
                }  
											//当右边第一个非终结符还未访问过的时候  
                if(firstVisit[k] == 0)  
                {  
                    Gene_first(k);  
                    firstVisit[k] = 1;  
                }  
                merge(first[i],first[k],2);		//如果first[k]此时有空值的话，暂时不把空值并入first[i]中  
                int r_Length = 0;  
                for(r_Length = 3;; r_Length++)  
                    if(pd_word[j][r_Length] == -1)  
                        break;  

												//到目前为止，只求出了右边的第一个(还不包括空的部分)，For循环处理之后的  
                for(k = 3; k<r_Length; k++)  
                {  
                    emptyRecu[0] = -1;//相当于初始化这个防递归集合  
  
												//如果右部的当前字符能推出空并且还不是最后一个字符，就将之后的一个字符并入First集中  
                    if(reduNull(pd_word[j][k]) == 1 && k<r_Length -1)  
                    {  
                        int u = 0;  
                        for(u=0;; u++)  
                        {  
												//注意是记录下一个符号的位置  
                            if(NotEndDic[u].second == pd_word[j][k+1])  
                            {  
                                break;  
                            }  
                        }  
                        if(firstVisit[u] == 0)  
                        {  
                            Gene_first(u);  
                            firstVisit[u] = 1;  
                        }  
                        merge(first[i],first[u],2);  
                    }  
													//到达最后一个字符，并且产生式右部都能推出空,将$并入First集中  
                    else if(reduNull(pd_word[j][k]) == 1 && k == r_Length -1)  
                    {  
                        int temp[2];  
                        temp[0] = GRAMMAR_NULL;  
                        temp[1] = -1;			
                        merge(first[i],temp,1);  
                    }  
                    else  
                    {  
                        break;  
                    }  
                }  
            }  
        }  
    }  
    firstVisit[i] = 1;						//设为已读
}  
void First()  
{  
											//先求出能直接推出空的非终结符集合  
    nullSet(GRAMMAR_NULL);  
    printf("\n");  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        Gene_first(i);  
    }  
    printf("\nFirst集：\n\n");  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        printf("First（%s） = ",NotEndDic[i].first);  
        for(int j=0;; j++)  
        {  
            if(first[i][j] == -1)  
            {  
                break;  
            }  
            printf("%s ",searchMapping(first[i][j]));  
        }  
        printf("\n");  
    }  
}  
											//将First结合起来的函数  
void connectFirstSet(int *p)  
{  
    int i = 0;  
    int flag = 0;  
    int temp[2];  
    //如果P的长度为1  
    if(p[1] == -1)  
    {  
        if(p[0] == GRAMMAR_NULL)  
        {  
            connectFirst[0] = GRAMMAR_NULL;  
            connectFirst[1] = -1;  
        }  
        else  
        {  
            for(i=0; i<NotEndDic.size(); i++)  
            {  
                if(NotEndDic[i].second == p[0])  
                {  
                    flag = 1;  
                    merge(connectFirst,first[i],1);  
                    break;  
                }  
            }  
            //也可能是终结符  
            if(flag == 0)  
            {  
                for(i=0; i<EndDic.size(); i++)  
                {  
                    if(EndDic[i].second == p[0])  
                    {  
                        temp[0] = EndDic[i].second;  
                        temp[1] = -1;  
                        merge(connectFirst,temp,2);//终结符的First集就是其本身  
                        break;  
                    }  
                }  
            }  
        }  
    }  
    //如果p的长度大于1  
    else  
    {  
        for(i=0; i<NotEndDic.size(); i++)  
        {  
            if(NotEndDic[i].second == p[0])  
            {  
                flag = 1;  
                merge(connectFirst,first[i],2);  
                break;  
            }  
        }  
        //也可能是终结符  
        if(flag == 0)  
        {  
            for(i=0; i<EndDic.size(); i++)  
            {  
                if(EndDic[i].second == p[0])  
                {  
                    temp[0] = EndDic[i].second;  
                    temp[1] = -1;  
                    merge(connectFirst,temp,2);//终结符的First集就是其本身  
                    break;  
                }  
            }  
        }  
        flag = 0;  
        int length = 0;  
        for(length = 0;; length++)  
        {  
            if(p[length] == -1)  
            {  
                break;  
            }  
        }  
        for(int k=0; k<length; k++)  
        {  
            emptyRecu[0] = -1;//相当于初始化这个防递归集合  
  
            //如果右部的当前字符能推出空并且还不是最后一个字符，就将之后的一个字符并入First集中  
            if(reduNull(p[k]) == 1 && k<length -1)  
            {  
                int u = 0;  
                for(u=0; u<NotEndDic.size(); u++)  
                {  
                    //注意是记录下一个符号的位置  
                    if(NotEndDic[u].second == p[k+1])  
                    {  
                        flag = 1;  
                        merge(connectFirst,first[u],2);  
                        break;  
                    }  
                }  
                //也可能是终结符  
                if(flag == 0)  
                {  
                    for(u=0; u<EndDic.size(); u++)  
                    {  
                        //注意是记录下一个符号的位置  
                        if(EndDic[u].second == p[k+1])  
                        {  
                            temp[0] = EndDic[i].second;  
                            temp[1] = -1;  
                            merge(connectFirst,temp,2);  
                            break;  
                        }  
                    }  
                }  
                flag = 0;  
            }  
            //到达最后一个字符，并且产生式右部都能推出空,将$并入First集中  
            else if(reduNull(p[k]) == 1 && k == length -1)  
            {  
                temp[0] = GRAMMAR_NULL;  
                temp[1] = -1;//其实是模拟字符串操作的手段  
                merge(connectFirst,temp,1);  
            }  
            else  
            {  
                break;  
            }  
        }  
    }  
}  
void Gene_follow(int i)  
{  
    int currentNon = NotEndDic[i].second;//当前的非终结符标号  
    int temp[2];  
    int result = 1;  
    temp[0] = currentNon;  
    temp[1] = -1;  
    merge(followRecu,temp,1);//将当前标号加入防递归集合中  
  
    //如果当前符号就是开始符号,把特殊符号加入其Follow集中  
    if(pd_word[1][1] == currentNon)  
    {  
        temp[0] = GRAMMAR_SPECIAL;//这个也是要处理的  
        temp[1] = -1;  
        merge(follow[i],temp,1);  
    }  
    for(int j = 1; j<=pd_num; j++) //j代表第几个产生式  
    {  
        //如果该非终结符在某个产生式的右部存在  
        if(inProcRight(currentNon,pd_word[j]) == 1)  
        {  
            int rightLength = 1;  
            int k = 0;//k为该非终结符在产生式右部的序号  
            int flag = 0;  
            int leftNum = pd_word[j][1];//产生式的左边  
            int h = 0;  
            int kArray[Max_Length2];  
            memset(kArray,-1,sizeof(kArray));  
            for(h = 0; h < NotEndDic.size(); h++)  
            {  
                if(NotEndDic[h].second == leftNum)  
                {  
                    break;  
                }  
            }  
			//先找到非终结符在非终极符表中位置
  
            for(rightLength = 1;; rightLength++)  
            {  
                if(currentNon == pd_word[j][rightLength+2])		//从3开始，若出现原非终结符，记下位置
                {  
                    kArray[k++] = rightLength;  
                }  
                if(pd_word[j][rightLength+2] == -1)  
                {  
                    break;  
                }  
            }  
            rightLength--;									//表达式右侧总长
            for(int y=0;; y++)  
            {  
                if(kArray[y] == -1)  
                {  
                    break;  
                }  
															//如果该非终结符在右部产生式的最后  
                if(kArray[y] == rightLength)  
                {  
  
                    if(inFollowRecu(leftNum) == 1)  
                    {  
                        merge(follow[i],follow[h],1);  
                        continue;  
                    }  
                    if(followVisit[h] == 0)  
                    {  
                        Gene_follow(h);  
                        followVisit[h] = 1;  
                    }  
                    merge(follow[i],follow[h],1);  
                }  
                //如果不在最后  
                else  
                {  
                    int n = 0;  
                    result = 1; 
                    for(n=kArray[y]+1; n<=rightLength; n++)  
                    {  
                        emptyRecu[0] = -1;  
                        result *= reduNull(pd_word[j][n+2]);  
                    }  
                    if(result == 1)  
                    {  
                        if(inFollowRecu(leftNum) == 1)  
                        {  
                            merge(follow[i],follow[h],1);				//对应情况：A->BC 且存在C->$
                            continue;  
                        }  
                        if(followVisit[h] == 0)  
                        {  
                            Gene_follow(h);  
                            followVisit[h] = 1;  
                        }  
                        merge(follow[i],follow[h],1);  
                    }  
                    int temp2[Max_Length];  
                    memset(temp2,-1,sizeof(temp2));  
                    for(n=kArray[y]+1; n<=rightLength; n++)  
                    {  
                        temp2[n-kArray[y]-1] = pd_word[j][n+2];  
                    }  
                    temp2[rightLength-kArray[y]] = -1;  
					connectFirst[0] = -1;								//重置
                    connectFirstSet(temp2);  
                    merge(follow[i],connectFirst,2);  
                }  
            }  
        }  
    }  
    followVisit[i] = 1;  
}  
  
//求所有非终结符的Follow集  
void Follow()  
{  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        followRecu[0] = -1;  
        Gene_follow(i);  
    }  
    printf("\nFollow集：\n\n");  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        printf("Follow（%s） = ",NotEndDic[i].first);  
        for(int j=0;; j++)  
        {  
            if(follow[i][j] == -1)  
            {  
                break;  
            }  
            printf("%s ",searchMapping(follow[i][j]));  
        }  
        printf("\n");  
    }  
}  
//求已经分解的产生式对应的Select集,注意Select集中不能含有空($),因而Type=2  
void Select()  
{  
    for(int i = 1; i<=pd_num; i++) //j代表第几个产生式  
    {  
        int leftNum = pd_word[i][1];	//产生式的左边  
        int h = 0;  
        int result = 1;  
        for(h = 0; h < NotEndDic.size(); h++)  
        {  
            if(NotEndDic[h].second == leftNum)  
            {  
                break;  
            }  
        }  
  
        int rightLength = 1;  
        for(rightLength = 1;; rightLength++)  
        {  
            if(pd_word[i][rightLength+2] == -1)  
            {  
                break;  
            }  
        }  
        rightLength--;  
        //如果右部推出式的长度为1并且是空,select[i-1] = follow[左边]  
        if(rightLength == 1 && pd_word[i][rightLength + 2] == GRAMMAR_NULL)  
        {  
            merge(select[i-1],follow[h],2);  
        }  
        //如果右部不是空的时候,select[i-1] = first[右部全部]  
        //如果右部能够推出空，select[i-1] = first[右部全部] ^ follow[左边]  
        else  
        {  
            int temp2[Max_Length];  
            int n = 0;  
            memset(temp2,-1,sizeof(temp2));  
            for(n=1; n<=rightLength; n++)  
            {  
                temp2[n-1] = pd_word[i][n+2];  
            }  
            temp2[rightLength] = -1;  
            connectFirst[0] = -1;//应该重新初始化一下  
            connectFirstSet(temp2);  
            merge(select[i-1],connectFirst,2);  
            for(n=1; n<=rightLength; n++)  
            {  
                emptyRecu[0] = -1;  
                result *= reduNull(pd_word[i][n+2]);  
            }  
            //如果右部能推出空，将follow[左边]并入select[i-1]中  
            if(result == 1)  
            {  
                merge(select[i-1],follow[h],2);  
            }  
        }  
    }  
    printf("\nSelect集：\n\n");  
    for(int i=0; i<pd_num; i++)  
    {  
        printf("Select（%d） = ",i+1);  
        for(int j=0;; j++)  
        {  
            if(select[i][j] == -1)  
            {  
                break;  
            }  
            printf("%s ",searchMapping(select[i][j]));  
        }  
        printf("\n");  
    }  
}  
//输出预测分析表  
void MTable()  
{  
    fstream outfile;  
    outfile.open("MTable.txt",ios::out);  
  
    for(int i=0; i<pd_num; i++)  
    {  
        int m = 0;//非终结符的序号  
        for(int t=0; t<NotEndDic.size(); t++)  
        {  
            if(NotEndDic[t].second == pd_word[i+1][1])  
            {  
                m = t;  
                break;  
            }  
        }  
  
        for(int j=0;; j++)  
        {  
            if(select[i][j] == -1)  
            {  
                break;  
            }  
            for(int k=0; k<EndDic.size(); k++)  
            {  
                if(EndDic[k].second == select[i][j])  
                {  
                    int n = 0;  
                    for(n=1; n<=Max_Length2; n++)  
                    {  
                        M[m][k][n-1] = pd_word[i+1][n];  
                        if(pd_word[i+1][n] == -1)  
                        {  
                            break;  
                        }  
                    }  
                    break;  
                }  
            }  
        }  
    }  
    //printf("\n*********************************预测分析表******************************\n\n");  
    outfile<<endl<<"*********************************预测分析表******************************"<<endl;  
    for(int i=0; i<NotEndDic.size(); i++)  
    {  
        for(int j=0; j<EndDic.size(); j++)  
        {  
            outfile<<"M["<<NotEndDic[i].first<<"]["<<EndDic[j].first<<"] = ";  
            //printf("M[%s][%s] = ",nonTerMap[i].first,terMap[j].first);  
            for(int k=0;; k++)  
            {  
                if(M[i][j][k] == -1)  
                {  
                    break;  
                }  
                outfile<<searchMapping(M[i][j][k]);  
                //printf("%s ",searchMapping(M[i][j][k]));  
            }  
            outfile<<endl;  
            //printf("\n");  
        }  
        outfile<<endl<<endl;  
        //printf("\n\n");  
    }  
    outfile.close();  
}  
  
void InitStack(SeqStack *S)    /*初始化顺序栈*/  
{  
    S->top = -1;  
}  
int Push(SeqStack *S,int x)   /*进栈*/  
{  
    if(S->top ==Stack_Size-1)  
        return 0;  
    S->top++;  
    S->elem[S->top]=x;  
    return 1;  
}  
int Pop(SeqStack *S)   /*出栈*/  
{  
    if(S->top==-1)  
        return 0;  
    else  
    {  
        S->top--;  
        return 1;  
    }  
}  
int GetTop(SeqStack *S,int *x)   /*取栈顶元素*/  
{  
    if(S->top==-1)  
        return 0;  
    else  
    {  
        *x=S->elem[S->top];  
        return 1;  
    }  
}  
void ShowStack1(SeqStack *S)   /*显示栈的字符，先输出栈底元素*/  
{  
  
    int i;  
    for(i=S->top; i>=0; i--)  
    {  
        //printf("%s ",searchMapping(S->elem[i]));  
        resultfile<<searchMapping(S->elem[i])<<" ";  
    }  
}  
void ShowStack2(SeqStack *S)   /*显示栈的字符，先输出栈顶元素*/  
{  
  
    int i;  
    for(i=S->top; i>=0; i--)  
    {  
        //printf("%s ",searchMapping(S->elem[i]));  
        resultfile<<searchMapping(S->elem[i])<<" ";  
    }  
}  
//分析源程序  
void Analysis()  
{  
    //分析结果输出  
  
    resultfile.open("result.txt",ios::out);  
  
    SeqStack s1,s2;  
    int c1,c2;  
    int i = 0;  
    int reserve[Stack_Size];//符号栈反向入栈  
    NormalNode * p = normalHead;  
    int s1Length = 0;  
    memset(reserve,-1,sizeof(reserve));  
  
    InitStack(&s1);  /*初始化符号栈和输入串*/  
    InitStack(&s2);  
    Push(&s1,GRAMMAR_SPECIAL);  
    Push(&s1,pd_word[1][1]);  
    Push(&s2,GRAMMAR_SPECIAL);  
  
    p = p->next;  
    while(p!=NULL)  
    {  
  
        if(p->type == AUTO || p->type == CONST || p->type == UNSIGNED || p->type == SIGNED  
                || p->type ==STATIC || p->type == VOLATILE )  
        {  
            reserve[i++] =  DESCRIBE;  
            //Push(&s2,DESCRIBE);  
        }  
        else if(p->type == INT_VAL)  
        {  
            reserve[i++] =  DIGIT;  
            //Push(&s2,DIGIT);  
        }  
        else if(p->type == CHAR || p->type == DOUBLE || p->type == FLOAT || p->type == INT ||  
                p->type == LONG || p->type == SHORT || p->type == VOID)  
        {  
            reserve[i++] =  TYPE;  
            //Push(&s2,TYPE);  
        }  
        else if(p->type == STRING_VAL)  
        {  
            reserve[i++] =  STRING;  
            //Push(&s2,STRING);  
        }  
        else if(p->type == DOU_QUE || p->type == SIN_QUE)  
        {  
  
        }  
        else  
        {  
            reserve[i++] =  p->type;  
            //Push(&s2,p->type);  
        }  
        p = p->next;  
    }  
    //求左边栈的长度  
    for(s1Length = 0;; s1Length++)  
    {  
        if(reserve[s1Length] == -1)  
        {  
            break;  
        }  
    }  
    //反向入栈  
    for(i = s1Length; i>0; i--)  
    {  
        Push(&s2,reserve[i-1]);  
    }  
  
    for(i=0;; i++)   /*分析*/  
    {  

        int flag = 0;  
        int h1;  
        int h2;  

        resultfile<<"第"<<i + 1<<"步"<<endl;  

        resultfile<<"栈1-符号栈:";  
        ShowStack1(&s1);  

        resultfile<<endl;  
  
        resultfile<<"栈2-输入栈:";  
        ShowStack2(&s2);  
        //printf("\n");  
        resultfile<<endl;  
  
        GetTop(&s1,&c1);   /*取栈顶元素，记为c1，c2*/  
        GetTop(&s2,&c2);  
        if(c1 == GRAMMAR_SPECIAL && c2 == GRAMMAR_SPECIAL)  /*当符号栈和输入栈都剩余#时，分析成功*/  
        {  

            resultfile<<"语法分析成功！"<<endl;  
            break;  
        }  
        if(c1 == GRAMMAR_SPECIAL && c2!= GRAMMAR_SPECIAL)  /*当符号栈剩余#，而输入串未结束时，分析失败 */  
        {  
            //printf("失败!\n");  
            resultfile<<"失败!"<<endl;  
            break;  
        }  
        if(c1 == c2)/*符号栈的栈顶元素和输入串的栈顶元素相同时，同时弹出*/  
        {  
            Pop(&s1);  
            Pop(&s2);  
            flag = 1;  
        }  
  
        else /*查预测分析表*/  
        {  
            //记录下非终结符的位置  
            for(h1=0; h1<NotEndDic.size(); h1++)  
            {  
                if(NotEndDic[h1].second == c1)  
                {  
                    break;  
                }  
            }  
            //记录下终结符的位置  
            for(h2=0; h2<EndDic.size(); h2++)  
            {  
                if(EndDic[h2].second == c2)  
                {  
                    break;  
                }  
            }  
            if(M[h1][h2][0] == -1)  
            {  
                //printf("Error\n");  
                resultfile<<"Error"<<endl;  
                break;//如果错误的话，直接终止分析  
            }  
            else  
            {  
                int length = 0;  
                //记录下推导式的长度  
                for(length = 0;; length++)  
                {  
                    if(M[h1][h2][length] == -1)  
                    {  
                        break;  
                    }  
                }  
                Pop(&s1);  
                //如果不是空的话，反向入栈  
                if(M[h1][h2][2] != GRAMMAR_NULL)  
                {  
                    for(int k = length-1; k>=2; k--)  
                    {  
                        Push(&s1,M[h1][h2][k]);  
                    }  
                }  
            }  
        }  
        if(flag == 1)  
        {   
            resultfile<<"该句成功匹配!"<<endl;  
        }  
        else  
        {  
            resultfile<<"产生式：";  
    
            int w = 0;  
            //记录下推导式的长度  
            for(w = 0;; w++)  
            {  
                if(M[h1][h2][w] == -1)  
                {  
                    break;  
                }  

                resultfile<<searchMapping(M[h1][h2][w]);  
            }  

            resultfile<<endl<<endl;  
        }  
    }  
    resultfile.close();  
	cout << "语法分析结果已经存入result.txt文件中！\n";
}  
