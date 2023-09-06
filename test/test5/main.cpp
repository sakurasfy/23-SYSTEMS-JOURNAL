#include<cstdio>
#include<cstring>
#include<algorithm>
#include<vector>
#include<queue>
#include<fstream>
#include<sstream>
#include<iostream>
#include<ctime>
#include<cstdlib>
#include <stdlib.h>
#include<limits.h>
#include<math.h>
#include<iterator>
#include <string>
#include<time.h>
#include<random>
#include <stdio.h>
#include <cryptopp/aes.h>
#include <cryptopp/filters.h>
#include <cryptopp/modes.h>
#include "paillier.h"
#include <openssl/sha.h>
#include <sys/time.h>  
//添加头文件
#define NODES_NUM 6549
#define EDGES_NUM 112666


using namespace std;
using namespace NTL;
ifstream infile;

double Time_HOP = 0.0;//hop索引表时间
double Time_ENHOP = 0.0;//hop索引加密时间
double Time_Eni = 0.0;//邻居索引表时间
double Time_ENEni = 0.0;//邻居索引加密时间
double UpdateNei = 0.0;//更新邻居索引表时间
double UpdateHop = 0.0;//更新二跳索引表时间
double Time_Query=0.0;
ZZ bignum = ZZ(10000000);

int64_t getCurrentTime()      //直接调用这个函数就行了，返回值最好是int64_t，long long应该也可以
{
	struct timeval tv;
	gettimeofday(&tv, NULL);    //该函数在sys/time.h头文件中
	return tv.tv_sec * 1000 + tv.tv_usec / 1000;
}

void InitTime() {
	Time_HOP = 0.0;
	Time_ENHOP = 0.0;
	Time_Eni = 0.0;//邻居索引表时间
	Time_ENEni = 0.0;//邻居索引加密时间
	UpdateNei = 0.0;//更新邻居索引表时间
	UpdateHop = 0.0;
	Time_Query=0.0;
}

byte key[CryptoPP::AES::DEFAULT_KEYLENGTH], iv[CryptoPP::AES::BLOCKSIZE];

void initKV()
{
	memset(key, 0x00, CryptoPP::AES::DEFAULT_KEYLENGTH);
	memset(iv, 0x00, CryptoPP::AES::BLOCKSIZE);

	// 或者也能够
	/*
	char tmpK[] = "1234567890123456";
	char tmpIV[] = "1234567890123456";
	for (int j = 0; j < CryptoPP::AES::DEFAULT_KEYLENGTH; ++j)
	{
		key[j] = tmpK[j];
	}

	for (int i = 0; i < CryptoPP::AES::BLOCKSIZE; ++i)
	{
		iv[i] = tmpIV[i];
	}
	*/
}
double timeCost(timespec start, timespec end) {//高分辨率计时器衡量性能

	timespec temp;
	if ((end.tv_nsec - start.tv_nsec) < 0) {// tv_nsec 纳秒数
		temp.tv_sec = end.tv_sec - start.tv_sec - 1;
		temp.tv_nsec = 1000000000 + end.tv_nsec - start.tv_nsec;
	}
	else {
		temp.tv_sec = end.tv_sec - start.tv_sec;//tv_sec 秒数
		temp.tv_nsec = end.tv_nsec - start.tv_nsec;
	}
	double ret;
	ret = (double)temp.tv_sec + (double)temp.tv_nsec / 1000000000;
	return ret;
}
struct Edge {
	int startNode;
	int endNode;
	ZZ weight;
};
vector<Edge>graph[NODES_NUM];//every vertex has a list of neighbour vertices
struct Label {//2-hop
	int self;
	int nextNode;
	ZZ distance;
};
vector<Label>HopIndex[NODES_NUM];//2-hop索引

struct Pair2 {
	int node;
	ZZ distance;
};
struct EnPair2 {
	string node;
	ZZ distance;
};

struct ENHop {
	string selfNode;
	string nextNode;
	ZZ distance;
};
struct ENNei {
	string selfNode;
	string nextNode;
	ZZ distance;
};
vector<ENHop>EnHopIndex[NODES_NUM];
vector<ENNei>EnNeiIndex[NODES_NUM];
ZZ Query(int v, int u, vector<Label> label[NODES_NUM]) {//只是用来建二跳索引！！！！真正查询两节点之间最短距离是PREFIXALQuery
	ZZ distance;
	vector<ZZ> tmp;
	if (v == u) {
		distance = bignum;
		return distance;
	}
	if (!label[v].empty() && !label[u].empty()) {
		for (int i = 0; i < label[v].size(); i++) {
			for (int j = 0; j < label[u].size(); j++) {
				if (label[v][i].nextNode == label[u][j].nextNode)
				{
					distance = label[v][i].distance + label[u][j].distance;
					tmp.push_back(distance);
				}
			}
		}
		distance = *min_element(tmp.begin(), tmp.end());
		return distance;
	}
	else {
		distance = bignum;
		return distance;
	}
}
void pruned_dijkstra_search(vector<Label> label[NODES_NUM], int startNode) {//pruned BFS search for 2-hop index
	queue<int>q;//扩展结点队列
	Pair2 P[NODES_NUM];

	for (int i = 0; i < NODES_NUM; i++) {
		P[i].distance = bignum;
	}
	P[startNode].distance = ZZ(0);

	q.push(startNode);//队列刚开始只有startNode
	while (!q.empty()) {
		int i = q.front(); //首元素出队
		q.pop();
		if (label[i].empty() || label[startNode].empty() ||
			((Query(startNode, i, label)) > P[i].distance)) {//从新扩展节点都节点i的路径比原索引中更好
			Label tmp;
			tmp.nextNode = startNode;
			tmp.distance = P[i].distance;
			tmp.self = i;
			label[i].push_back(tmp);//节点i加入索引		
			for (int j = 0; j < graph[i].size(); j++) {//节点i的邻居节点u
				if ((P[graph[i][j].endNode].distance == bignum)&&(graph[i][j].endNode>startNode)) {//节点u没被访问过
					P[graph[i][j].endNode].distance = P[i].distance + 1;
					q.push(graph[i][j].endNode);//将满足条件的节点u放进队列
				}
			}
		}
		else {
			continue;//原索引中的路径更好
		}
	}
	for (int i = 0; i < NODES_NUM; i++) {
		HopIndex[i] = label[i];//更新索引
	}
}
void Initgraph(const char* graphfile) {//for 2-hop
	freopen(graphfile, "r", stdin);//打开数据
	for (int i = 0; i < EDGES_NUM; i++) {//将文件中的边读进graph
		int x, y;
		scanf("%d%d", &x, &y);
		Edge tmp1, tmp2;
		tmp1.startNode = x-1;
		tmp1.endNode = y-1;
		tmp1.weight = ZZ(1);
		graph[x-1].push_back(tmp1);
		tmp2.startNode = y-1;
		tmp2.endNode = x-1;
		tmp2.weight = tmp1.weight;
		graph[y-1].push_back(tmp2);
	}
	fclose(stdin);
}
void BuildHopIndex() {//建立2-hop
	for (int i = 0; i < NODES_NUM; i++) {
		pruned_dijkstra_search(HopIndex, i);
		cout << "节点" << i << "标签完成" << endl;
	}
}
ZZ PREFIXALQuery(int vk, int v) {//去掉了下标小于k
	ZZ distance;
	vector<ZZ> tmp;
	if (vk == v) {
		distance = ZZ(0);
	}
	else {
		for (int i = 0; i < HopIndex[vk].size(); i++) {
			for (int j = 0; j < HopIndex[v].size(); j++) {
				if (HopIndex[vk][i].nextNode == HopIndex[v][j].nextNode)
				{
					distance = (HopIndex[vk][i].distance + HopIndex[v][j].distance);
					//p.cost = (label[v][i].cost + label[u][j].cost);
					tmp.push_back(distance);
				}
			}
			distance = *min_element(tmp.begin(), tmp.end());
		}
	}
	return distance;
}
void ResumePBFS(int vk, int u, ZZ d) {
	queue<Pair2> Q;
	Pair2 temp, temp2;
	temp.node = u;
	temp.distance = d;
	Q.push(temp);
	while (!Q.empty()) {
		int v = Q.front().node;
		ZZ d1 = Q.front().distance;
		Q.pop();
		if (PREFIXALQuery(vk, v) > d1) {

			Label tmp;
			tmp.self = v;
			tmp.nextNode = vk;
			tmp.distance = d1;
			HopIndex[v].push_back(tmp);
			for (int j = 0; j < graph[v].size(); j++) {
				temp2.node = graph[v][j].endNode;
				temp2.distance = d1 + 1;
				Q.push(temp2);
			}
		}
	}
}
void Insertedge(int x, int y) {
	for (int i = 0; i < HopIndex[x].size(); i++) {
		ResumePBFS(HopIndex[x][i].nextNode, y, Query(HopIndex[x][i].nextNode, x, HopIndex) + 1);
		//std::cout << "nowTime: " << getCurrentTime() << "\n";
	}
	for (int i = 0; i < HopIndex[y].size(); i++) {
		ResumePBFS(HopIndex[y][i].nextNode, x, Query(HopIndex[y][i].nextNode, y, HopIndex) + 1);
		//std::cout << "nowTime: " << getCurrentTime() << "\n";
	}
}
int Size() {//统计最大度数
	int size = 0;
	for (int i = 0; i < NODES_NUM; i++) {//统计最大度

		if (graph[i].size() > size) {
			size = graph[i].size();
		}
	}
	return size;
}
vector<Edge> Neighbor[NODES_NUM];//neighbor表
void BuildNeighbor() {//建立填充的邻接表
	int size = Size();
	Edge temp;
	for (int i = 0; i < NODES_NUM; i++) {
		for (int y = 0; y < graph[i].size(); y++) {
			temp.startNode = graph[i][y].startNode;
			temp.endNode = graph[i][y].endNode;
			temp.weight = ZZ(graph[i][y].weight);
			Neighbor[i].push_back(temp);
		}
		if (Neighbor[i].size() < size) {//填充
			for (int y = Neighbor[i].size(); y < size + 1; y++) {
				int end = rand() % NODES_NUM;
				temp.startNode = i;
				temp.endNode = end;
				temp.weight = bignum;
				Neighbor[i].push_back(temp);
			}
		}
	}
}
string sha256(const string str)//伪随机加密
{
	char buf[2000];
	unsigned char hash[SHA256_DIGEST_LENGTH];
	SHA256_CTX sha256;
	SHA256_Init(&sha256);
	SHA256_Update(&sha256, str.c_str(), str.size());
	SHA256_Final(hash, &sha256);
	std::string NewString = "";
	for (int i = 0; i < SHA256_DIGEST_LENGTH; i++)
	{
		sprintf(buf, "%02x", hash[i]);
		NewString = NewString + buf;
	}
	return NewString;
}
Paillier paillier(512);
string Enc(int a)
{
	string plainText;
	plainText = to_string(a);
	string cipherText;
	//
	CryptoPP::AES::Encryption aesEncryption(key, CryptoPP::AES::DEFAULT_KEYLENGTH);
	CryptoPP::CBC_Mode_ExternalCipher::Encryption cbcEncryption(aesEncryption, iv);
	CryptoPP::StreamTransformationFilter stfEncryptor(cbcEncryption, new CryptoPP::StringSink(cipherText));
	stfEncryptor.Put(reinterpret_cast<const unsigned char*>(plainText.c_str()), plainText.length() + 1);
	stfEncryptor.MessageEnd();
	string cipherTextHex;
	for (int i = 0; i < cipherText.size(); i++)
	{
		char ch[3] = { 0 };
		sprintf(ch, "%02x", static_cast<byte>(cipherText[i]));
		cipherTextHex += ch;
	}
	return cipherTextHex;
}
string DecEnc(string cipherTextHex)
{
	string cipherText;
	string decryptedText;
	int i = 0;
	while (true)
	{
		char c;
		int x;
		stringstream ss;
		ss << hex << cipherTextHex.substr(i, 2).c_str();
		ss >> x;
		c = (char)x;
		cipherText += c;
		if (i >= cipherTextHex.length() - 2)break;
		i += 2;
	}

	CryptoPP::AES::Decryption aesDecryption(key, CryptoPP::AES::DEFAULT_KEYLENGTH);
	CryptoPP::CBC_Mode_ExternalCipher::Decryption cbcDecryption(aesDecryption, iv);
	CryptoPP::StreamTransformationFilter stfDecryptor(cbcDecryption, new CryptoPP::StringSink(decryptedText));
	stfDecryptor.Put(reinterpret_cast<const unsigned char*>(cipherText.c_str()), cipherText.size());
	stfDecryptor.MessageEnd();
	return decryptedText;
}

void EnHop() {//加密二跳索引
	string node;
	ZZ distance;
	for (int i = 0; i < NODES_NUM; i++) {
		for (int j = 0; j < HopIndex[i].size(); j++) {
			//加密头节点
			node = to_string(HopIndex[i][j].self);//伪随机加密头结点
			node = sha256(node);
			ENHop tmp;
			tmp.selfNode = node;
			unsigned char nextnode[128];
			tmp.nextNode = Enc(HopIndex[i][j].nextNode);
			distance = HopIndex[i][j].distance;//同态加密距离值
			tmp.distance = paillier.encrypt(distance);
			EnHopIndex[i].push_back(tmp);

		}
		cout << "节点" << i << "二跳索引加密完成!" << endl;
	}
}
void EnNei() {//加密填充的邻居节点
	string node;
	string nextnode;
	ZZ distance;
	for (int i = 0; i < NODES_NUM; i++) {

		for (int j = 0; j < Neighbor[i].size(); j++) {
			node = sha256(to_string(Neighbor[i][j].startNode));//伪随机加密头结点
			nextnode = sha256(to_string(Neighbor[i][j].endNode));
			distance = paillier.encrypt(Neighbor[i][j].weight);
			ENNei tmp;
			tmp.selfNode = node;
			tmp.nextNode = nextnode;
			tmp.distance = distance;
			EnNeiIndex[i].push_back(tmp);
		}
		cout << "节点" << i << "邻居索引加密完成!" << endl;
	}
}
int Com(ZZ a, ZZ b) {//密文比较协议,a,b是两个密文 算a-b
	ZZ cb = InvMod(b, paillier.modulus * paillier.modulus);//计算-b
	/*ZZ m5 = PowerMod(ZZ(2), 32, paillier.modulus * paillier.modulus);//2^l+b-a
	ZZ hh = paillier.encrypt(m5);
	ZZ m6 = paillier.add(a, hh);
	ZZ c7 = paillier.add(m6, cb);
	ZZ m7 = paillier.decrypt(c7);
	cout << "m7=" << m7 << endl;
	ZZ m8 = RightShift(m7, 32);
	cout << "有效位 = " << bit(m8, 0) << endl;
	return bit(m8, 0);*/
	ZZ m5 = paillier.add(a, cb);//a-b靠近0还是靠近n
	ZZ c5 = paillier.decrypt(m5);
	//cout << "差=" << c5 << endl;
	if (c5 > 1000000)
		return 1;//b大于a
	else
		return 0;//b小于等于a

	/*ZZ aa = paillier.decrypt(a);
	ZZ bb = paillier.decrypt(b);
	if (a < b)
		return 1;
	else
		return 0;*/

}

ZZ Query2(string v, string u) {//密文下查询两点之间距离值返回一个加密值
	ZZ distance= paillier.encrypt(bignum);
	vector<ZZ> tmp;
	//std::cout << "nowTime: " << getCurrentTime() << "\n";
	if (v == u) {
		distance = paillier.encrypt(ZZ(0));
		return distance;
	}
	int x, y;
	for (int i = 0; i < NODES_NUM; i++) {

		if (EnHopIndex[i][0].selfNode == v)
		{
			x = i;
			//cout << "x=" << x << endl;
		}
		if (EnHopIndex[i][0].selfNode == u)
		{
			y = i;
			//cout << "y=" << y << endl;
		}
	}

	if (!EnHopIndex[x].empty() && !EnHopIndex[y].empty()) {
		
		for (int i = 0; i < EnHopIndex[x].size(); i++) {
			//cout << "there1" << endl;
			for (int j = 0; j < EnHopIndex[y].size(); j++) {
				//cout << "there2" << endl;
				if (EnHopIndex[x][i].nextNode == EnHopIndex[y][j].nextNode)
				{

					distance = paillier.add(EnHopIndex[x][i].distance, EnHopIndex[y][j].distance);
					//cout << "距离3=" << paillier.decrypt(distance) << endl;
					tmp.push_back(distance);
				}
			}
		}

		//多次运行比较协议找到最小值
		if (tmp.size() == 0) {
		
			distance = paillier.encrypt(bignum);
			return distance;
		}
		if (tmp.size() == 1) {
			//cout << "distance1=" << paillier.decrypt(tmp[0]) << endl;
			return tmp[0];
		}
		else {
			ZZ min = tmp[0];
			for (int i = 1; i < tmp.size(); i++) {

				if (Com(tmp[i], min))
				{
					min = tmp[i];
				}
			}
			//cout << "distance2="<< paillier.decrypt(min) << endl;
			return min;
		}
	}
	else {
		distance = paillier.encrypt(bignum);
		//cout << "distance3=" << paillier.decrypt(distance) << endl;
		return distance;
	}
}
int yyy = 0;
void EnResumePBFS(string vk, string u, ZZ d, string vkenc) {//vk和u是lab vkenc是enc
	queue<EnPair2> Q;
	EnPair2 temp, temp2;
	temp.node = u;
	temp.distance = d;
	Q.push(temp);
	
	while (!Q.empty()) {
		//cout << "okkk" << endl;
		string v = Q.front().node;
		ZZ d1 = Q.front().distance;
		//cout << "距离1=" << paillier.decrypt(d1) << endl;
		Q.pop();
		ZZ tt = paillier.encrypt(bignum);
		//cout << "距离2=" << paillier.decrypt(tt) << endl;
		tt=Query2(vk, v);
		
		int uo = (Com(d1, Query2(vk, v)) && Com(d1, paillier.encrypt(bignum)));
		if (Com(d1, Query2(vk, v)) && Com(d1, paillier.encrypt(bignum))) {

			ENHop tmp;
			//新增的lab要转成enc
			tmp.selfNode = v;
			tmp.nextNode = vkenc;
			//cout << "新加的=" << DecEnc(vkenc) << endl;
			//统计新增多少项
			yyy = yyy + 1;
			tmp.distance = d1;
			//cout << "距离=" << paillier.decrypt(d1) << endl;
			int x;
			for (int i = 0; i < NODES_NUM; i++) {

				if (EnHopIndex[i][0].selfNode == v)
				{
					x = i;
				}
			}
			EnHopIndex[x].push_back(tmp);

			for (int j = 0; j < EnNeiIndex[x].size(); j++) {
				temp2.node = EnNeiIndex[x][j].nextNode;
				ZZ c1 = EnNeiIndex[x][j].distance;
				//cout << "c1=" << c1 << endl;
				temp2.distance = paillier.add(d1, c1);
				Q.push(temp2);
			}
		}
		else {
			continue;
		}

	}
}
void EnInsertedge(string s, string t) {//密文下插入
	int x, y;
	for (int i = 0; i < NODES_NUM; i++) {

		if (EnHopIndex[i][0].selfNode == s)
		{
			x = i;
			//cout << "x=" <<x<< endl;
		}
		if (EnHopIndex[i][0].selfNode == t)
		{
			y = i;
			//cout << "y=" <<y<< endl;
		}
	}
	ZZ c1 = paillier.encrypt(ZZ(1));
	for (int i = 0; i < EnHopIndex[x].size(); i++) {
		string nextnode = sha256(DecEnc(EnHopIndex[x][i].nextNode).data());
		ZZ c2 = Query2(nextnode, s);
		//cout << "ok=" << paillier.decrypt(c2) << endl;
		EnResumePBFS(nextnode, t, paillier.add(c2, c1), EnHopIndex[x][i].nextNode);
		//cout << "ok1" << endl;
		//std::cout << "nowTime: " << getCurrentTime() << "\n";
	}
	for (int i = 0; i < HopIndex[y].size(); i++) {
		string nextnode = sha256(DecEnc(EnHopIndex[y][i].nextNode).data());
		ZZ c2 = Query2(nextnode, t);
		EnResumePBFS(nextnode, s, paillier.add(c2, c1), EnHopIndex[y][i].nextNode);
		//cout << "ok1" << endl;
		//std::cout << "nowTime: " << getCurrentTime() << "\n";
	}
}
struct InsertToken {
	string s;
	string t;
};
InsertToken IT;
void InsertTokenGen(int a, int b) {
	string s, t;
	s = to_string(a);//伪随机加密头结点
	IT.s = sha256(s);
	t = to_string(b);//伪随机加密头结点
	IT.t = sha256(t);
}
void UpdateNeiIndex(string a, string b) {//更新邻居索引
	for (int i = 0; i < NODES_NUM; i++) {
		//std::cout << "nowTime: " << getCurrentTime() << "\n";
		if (EnNeiIndex[i][0].selfNode == a) {
			ENNei tmp;
			tmp.selfNode = a;
			tmp.nextNode = b;
			ZZ c = paillier.encrypt(ZZ(1));
			tmp.distance = c;
			EnNeiIndex[i].push_back(tmp);
		}
		if (EnNeiIndex[i][0].selfNode == b) {
			ENNei tmp;
			tmp.selfNode = b;
			tmp.nextNode = a;
			ZZ c = paillier.encrypt(ZZ(1));
			tmp.distance = c;
			EnNeiIndex[i].push_back(tmp);
		}
	}
}

int main(int argc, char** argv) {
	timespec beginT, endT;
	int EnHopsize, UpdateHopsize, EnNeisize, UpdateNeisize;
	const char* graphfile = "./graph/FR.in";
	initKV();
	Initgraph(graphfile);//初始化把图读进来
	/*for (int i = 0; i < NODES_NUM; i++)//显示图
	{
		for (int j = 0; j < graph[i].size(); j++) {
			cout << "graph[" << i << "][" << j << "]=(" << graph[i][j].startNode << " " << graph[i][j].endNode << " " << graph[i][j].weight << ")" << endl;
		}
		cout << endl;
	}*/
	cout << "系统初始化完成！" << endl;
	cout << endl;

	//建填充的邻居节点
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
	BuildNeighbor();
	/*for (int i = 0; i < NODES_NUM; i++) {//显示填充的邻居表
		for (int j = 0; j <Neighbor[i].size(); j++) {
			cout << "Neighbor[" << i << "][" << j << "]=(" << Neighbor[i][j].startNode << " " << Neighbor[i][j].endNode << " " << Neighbor[i][j].weight << ")" << endl;
		}
		printf("\n");
	}*/
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
	Time_Eni += timeCost(beginT, endT);
	cout << "建立填充邻居索引完成！" << endl;
	cout << endl;

	//建二跳索引
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
	BuildHopIndex();
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
	Time_HOP += timeCost(beginT, endT);
	cout << "建立二跳索引完成！" << endl;
	cout << endl;
	for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j < HopIndex[i].size(); j++) {
			cout << "HopIndex[" << i << "][" << j << "]=(" << HopIndex[i][j].self << " " << HopIndex[i][j].nextNode << " " << HopIndex[i][j].distance << ")" << endl;
		}
		printf("\n");
	}

	//加密二跳索引
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
	EnHop();
	/*for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j <  EnHopIndex[i].size(); j++) {
			cout << "EnHopIndex[" << i << "][" << j << "="<< EnHopIndex[i][j].nextNode << endl;
		}
		printf("\n");
	}*/
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
	Time_ENHOP += timeCost(beginT, endT);
	//统计原始加密二跳索引大小
	int size = 0;
	for (int i = 0; i < NODES_NUM; i++) {
		size = size + EnHopIndex[i].size();
	}
	EnHopsize = size * sizeof(ENHop)>>20;
	int d=size * sizeof(ENHop)>>10;
	cout << "加密二跳索引完成！" << endl;
	cout << endl;

	//加密邻居索引
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
	EnNei();
	/*for (int i = 0; i < NODES_NUM; i++) {//显示加密的邻居索引
		for (int j = 0; j < EnNeiIndex[i].size(); j++) {
			cout << "EnNeiIndex[" << i << "][" << j << "]=(" << EnNeiIndex[i][j].selfNode << " " << EnNeiIndex[i][j].nextNode << " " << EnNeiIndex[i][j].distance << ")" << endl;
		}
		printf("\n");
	}*/
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
	Time_ENEni += timeCost(beginT, endT);
	//统计原始邻居索引大小
	size = 0;
	for (int i = 0; i < NODES_NUM; i++) {
		size = size + EnNeiIndex[i].size();
	}
	EnNeisize = size * sizeof(ENNei)>>20;
	int c=size * sizeof(ENNei)>>10;
	cout << "加密邻居索引完成！" << endl;
	cout << endl;
	//明文添加!!!!!!!!明文添加没有更新邻居节点就是graph！！！不想写了
	/*Insertedge(2, 7);
	for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j < HopIndex[i].size(); j++) {
			cout << "HopIndex[" << i << "][" << j << "]=(" << HopIndex[i][j].self << " " << HopIndex[i][j].nextNode << " " << HopIndex[i][j].distance << ")" << endl;
		}
		printf("\n");
	}
	/*Insertedge(9, 11);
	for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j < HopIndex[i].size(); j++) {
			printf("2HopIndex[%d][%d]=(%d,%d,%llu)\n", i, j, HopIndex[i][j].self, HopIndex[i][j].nextNode, HopIndex[i][j].distance);
		}
		printf("\n");
	}
	*/

	//密文插入陷门生成
	//单个插入

	/*InsertTokenGen(2, 7);

	//更新邻居索引
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
	UpdateNeiIndex(IT.s, IT.t);
	cout << "邻居更新" << endl;
	/*for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j < EnNeiIndex[i].size(); j++) {
			cout << "EnNeiIndex[" << i << "][" << j << "]=(" << EnNeiIndex[i][j].nextNode << "   ||   " << paillier.decrypt(EnNeiIndex[i][j].distance) << ")" << endl;
		}
		printf("\n");
	}
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
	UpdateNei += timeCost(beginT, endT);

	//更新二跳索引
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
	EnInsertedge(IT.s, IT.t);
	cout << "二跳更新完成" << endl;
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
	UpdateHop += timeCost(beginT, endT);

	//cout << "finish" << endl;
	//显示解密的新增的二跳索引
	/*for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j < EnHopIndex[i].size(); j++) {
			cout << "EnHopIndex[" << i << "][" << j << "]=(" << DecEnc(EnHopIndex[i][j].nextNode)<< " " << paillier.decrypt(EnHopIndex[i][j].distance) << ")" << endl;
		}
		printf("\n");
	}

	/*InsertTokenGen(9, 11);
	//cout << "ok" << endl;
	cout << "s=" << IT.s << endl;
	cout << "t=" << IT.t << endl;
	EnInsertedge(IT.s, IT.t);
	cout << "finish" << endl;
	//显示解密的新增的二跳索引
	/*for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j < EnHopIndex[i].size(); j++) {
			cout << "EnHopIndex[" << i << "][" << j << "]=(" << DecEnc(EnHopIndex[i][j].nextNode) << " " << paillier.decrypt(EnHopIndex[i][j].distance) << ")" << endl;
		}
		printf("\n");
	}*/

	//批量更新
	for (int i = 0; i < 5; i++) {
		unsigned seed;
		seed=time(0);
		srand(seed);
		int a = rand() % NODES_NUM;
		int b = rand() % NODES_NUM;
		InsertTokenGen(a, b);

		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
		UpdateNeiIndex(IT.s, IT.t);
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
		UpdateNei += timeCost(beginT, endT);

		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
		//cout << "第 " << i<<"次更新邻居索引完成！"<<endl;
		EnInsertedge(IT.s, IT.t);
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);

		UpdateHop += timeCost(beginT, endT);
		cout << "第" << i + 1 << "次插入完成！" << endl;
	}
	//显示最后的二跳索引
	/*for (int i = 0; i < NODES_NUM; i++) {//显示2-hop index
		for (int j = 0; j < EnHopIndex[i].size(); j++) {
			cout << "EnHopIndex[" << i << "][" << j << "]=(" << DecEnc(EnHopIndex[i][j].nextNode) << " " << paillier.decrypt(EnHopIndex[i][j].distance) << ")" << endl;
		}
		printf("\n");
	}*/
	//统计更新后二跳索引大小
	size = 0;
	for (int i = 0; i < NODES_NUM; i++) {
		size = size + EnHopIndex[i].size();
	}
	UpdateHopsize = size * sizeof(ENHop)>>20;
	int b=size * sizeof(ENHop)>>10;
	//统计更新后邻居索引大小
	size = 0;
	for (int i = 0; i < NODES_NUM; i++) {
		size = size + EnNeiIndex[i].size();
	}
	UpdateNeisize = size * sizeof(ENNei)>>20;
	int a=size * sizeof(ENNei)>>10;

	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &beginT);
	for(int i=0;i<100;i++){
		unsigned seed;
		seed=time(0);
		srand(seed);
		int a = rand() % NODES_NUM;
		int b = rand() % NODES_NUM;
		InsertTokenGen(a, b);
		ZZ d=Query2(IT.s, IT.t);
		cout<<"距离="<<paillier.decrypt(d)<<endl;;
	}
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &endT);
	Time_Query += timeCost(beginT, endT);
	
	cout<<"数据集："<<graphfile<<endl;
	cout << "节点数：" << NODES_NUM << endl;
	cout << "边数：" << EDGES_NUM << endl;
	cout << "建二跳索引时间：" << Time_HOP << endl;
	cout << "加密二跳索引时间：" << Time_ENHOP << endl;
	cout << "建邻居索引时间：" << Time_Eni << endl;
	cout << "加密邻居索引时间：" << Time_ENEni << endl;
	cout << "查询100次时间：" << Time_Query << endl;
	cout << "更新10次加密邻居索引时间：" << UpdateNei << endl;
	cout << "更新10次加密二跳索引时间：" << UpdateHop << endl;
	
	cout << "原始加密二跳索引大小(MB)" << EnHopsize << endl;
	cout << "原始加密二跳索引大小(KB)" << d << endl;
	
	cout << "更新后加密二跳索引大小(MB)" << UpdateHopsize << endl;
	cout << "更新后加密二跳索引大小(KB)" << b << endl;
	
	cout << "原始加密邻居索引大小(MB)" << EnNeisize << endl;
	cout << "原始加密邻居索引大小(KB)" << c << endl;
	
	cout << "更新后加密邻居索引大小(MB)" << UpdateNeisize << endl;
	cout << "更新后加密邻居索引大小(KB)" << a << endl;
	
	cout << "新增" << yyy << "项" << endl;


	return(0);
}