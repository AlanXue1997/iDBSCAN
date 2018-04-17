#include <cstdio>
#include <time.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <Windows.h>
#include <stack>
#include <algorithm>
#include <math.h>

//#define DEBUG
//#define MULTI	//Won't process missing data

#define pointSet std::vector<Point*>

#define MAX_FIND 100
#define epsilon 0.0000001
#define sample_n 1000
#define NOT_VISITED -1
#define VISITED 1
#define MAX_CLUSTER 100
#define INFINITE 10000

#define ATTRIBUTIONS 3
#define CLUSTER 2	//Number of original clusters / Number of label types

#define K 4

class UnionFindSet {
private:
	int *f;
public:
	int father(int k) {
		return f[k] == k ? k : (f[k] = father(f[k]));
	}
	UnionFindSet(int n) {
		f = new int[n];
		for (int i = 0; i < n; ++i) {
			f[i] = i;
		}
	}
	void connect(int i, int j) {
		f[father(i)] = father(j);
	}
	bool query(int i, int j) {
		return father(i) == father(j);
	}
};

class Point {
public:
	static int Number;
	double a[ATTRIBUTIONS];
	Point() {
		ddrs = NULL;
		flag = NOT_VISITED;
		incomplete = 0;
		num = Number++;
	}
	int num;
	int flag;
	int flag_ans;
	int incomplete;
	int Nddrs;
	pointSet *ddrs;
};

class TREE_Point {
public:
	Point *point;
	int d;
	TREE_Point *l, *r;
};

double distance(Point *a, Point *b) {
	double ans = 0;
	for (int i = 0; i < ATTRIBUTIONS; ++i) {
		ans += (a->a[i] - b->a[i])*(a->a[i] - b->a[i]);
	}
	return sqrt(ans);
}

double pseDistance(Point *a, Point *b) {
	double ans = 0;
	bool p = false;
	for (int i = 0; i < ATTRIBUTIONS; ++i) {
		if (b->a[i] < INFINITE - 1) {
			p = true;
			ans += (a->a[i] - b->a[i])*(a->a[i] - b->a[i]);
		}
	}
	return p?sqrt(ans):INFINITE;
}

class KD_TREE {
private:
	TREE_Point* root;
	double E;
	int findSplit(pointSet *set) {
		double var[ATTRIBUTIONS];
		double sum[ATTRIBUTIONS];
		memset(var, 0, sizeof(var));
		memset(sum, 0, sizeof(sum));
		for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
			for (int j = 0; j < ATTRIBUTIONS; ++j) {
				sum[j] += (*i)->a[j];
			}
		}
		for (int j = 0; j < ATTRIBUTIONS; ++j) {
			sum[j] /= set->size();
		}
		for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
			for (int j = 0; j < ATTRIBUTIONS; ++j) {
				var[j] += ((*i)->a[j] - sum[j])*((*i)->a[j] - sum[j]);
			}
		}
		int k = 0;
		for (int i = 1; i < ATTRIBUTIONS; ++i) {
			if (var[k] < var[i]) k = i;
		}
		for (int i = 1; i < set->size(); ++i) {
			int j = i;
			while (j > 0 && set->at(j - 1)->a[k] > set->at(j)->a[k]) {
				std::swap(set->at(j - 1), set->at(j));
				j--;
			}
		}
		return k;
	}

	void findNeighbor(pointSet *set, TREE_Point *p, Point *point) {
		double dis = distance(p->point, point);
		if (dis < E && dis > epsilon) set->push_back(p->point);
		if (point->a[p->d] < p->point->a[p->d]) {
			if (p->l != NULL) findNeighbor(set, p->l, point);
			if (p->r != NULL && (p->point->a[p->d] - point->a[p->d]) < E) findNeighbor(set, p->r, point);
		}
		else {
			if (p->r != NULL) findNeighbor(set, p->r, point);
			if (p->l != NULL && (point->a[p->d] - p->point->a[p->d]) < E) findNeighbor(set, p->l, point);
		}
	}

	TREE_Point* construct(pointSet *set) {
		TREE_Point* p = new TREE_Point();
		if (set->size() == 0) return NULL;
		if (set->size() == 1) {
			p->d = -1;
			p->l = p->r = NULL;
			p->point = set->at(0);
			return p;
		}
		pointSet* sample = new pointSet();
		if (set->size() <= sample_n) {
			sample = set;
		}
		else {
			for (int i = 0; i < set->size(); ++i) {
				if (rand() % (set->size() - i) < (sample_n - sample->size())) {
					sample->push_back(set->at(i));
				}
				if (sample->size() == sample_n) break;
			}
		}
		p->d = findSplit(sample);
		p->point = sample->at(sample->size() / 2);
		pointSet* lset;
		pointSet* rset;
		if (set->size() <= sample_n)
		{
			lset = new pointSet(set->size() / 2);
			std::copy(set->begin(), set->begin() + set->size() / 2, lset->begin());
			if (set->size() > 2) {
				rset = new pointSet(set->size() - set->size() / 2 - 1);
				std::copy(set->begin() + set->size() / 2 + 1, set->end(), rset->begin());
			}
			else {
				rset = NULL;
			}
			delete set;
			p->l = construct(lset);
			if (rset != NULL) {
				p->r = construct(rset);
			}
			else {
				p->r = NULL;
			}
		}
		else {
			delete sample;
			lset = new pointSet();
			rset = new pointSet();
			int mark = 0;
			for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
				int &k = p->d;
				if ((*i)->a[k] < p->point->a[k]) {
					lset->push_back(*i);
				}
				else if ((*i)->a[k] > p->point->a[k]) {
					rset->push_back(*i);
				}
				else {
					if (mark) {
						lset->push_back(*i);
					}
					else {
						rset->push_back(*i);
					}
					mark = !mark;
				}
			}
			delete set;
			p->l = construct(lset);
			p->r = construct(rset);
		}
		return p;
	}

	void findPredict(pointSet *neighbors, TREE_Point *p, Point *point, int d) {
		if (p == NULL) return;
		double dis = pseDistance(p->point, point);
		if (dis < E) {
			dis = sqrt(E*E - dis*dis);
			neighbors->push_back(p->point);
		}
		if (point->a[p->d] != INFINITE) {
			if (point->a[p->d] < p->point->a[p->d]) {
				findPredict(neighbors, p->l, point, d);
				if (p->point->a[p->d] - point->a[p->d] < E) findPredict(neighbors, p->r, point, d);
			}
			else {
				findPredict(neighbors, p->r, point, d);
				if (point->a[p->d] - p->point->a[p->d] < E) findPredict(neighbors, p->l, point, d);
			}
		}
		else {
			findPredict(neighbors, p->r, point, d);
			findPredict(neighbors, p->l, point, d);
		}
	}

	void update(Point *point, UnionFindSet *ufs) {
		pointSet *set = neighbor(point, E);
		point->Nddrs = set->size();
		point->ddrs = set;
		for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
			if ((*i) != point) {
				(*i)->Nddrs++;
				(*i)->ddrs->push_back(point);
				if ((*i)->Nddrs >= K && point->Nddrs >= K) {
					ufs->connect(point->num, (*i)->num);
				}
			}
		}
		for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
			if ((*i) != point && (*i)->Nddrs == K){
				pointSet *neighborSet = (*i)->ddrs;
				for (pointSet::iterator j = neighborSet->begin(); j != neighborSet->end(); ++j) {
					if ((*j)->Nddrs >= K) {
						ufs->connect((*i)->num, (*j)->num);
					}
				}
			}
		}
	}

public:
	KD_TREE(pointSet *set) {
		pointSet *set_copy = new pointSet(set->size());
		std::copy(set->begin(), set->end(), set_copy->begin());
		root = new TREE_Point();
		root->r = construct(set_copy);
	}

	pointSet* neighbor(Point *point, double E) {
		pointSet *set = new pointSet();
		this->E = E;
		if (root->r != NULL) findNeighbor(set, root->r, point);
		return set;
	}

	double predict(Point *point, double E, int d, UnionFindSet *ufs) {
		this->E = E;
		pointSet *neighbors = new pointSet();
		findPredict(neighbors, root->r, point, d);
		double min_length = -INFINITE;
		double min_p = 0;
		Point *represent = NULL;
		std::set<int> visited;
		for (pointSet::iterator i = neighbors->begin(); i != neighbors->end(); ++i) {
			if (visited.find(ufs->father((*i)->num)) == visited.end()) {
				visited.insert(ufs->father((*i)->num));
				int total = 0;
				Point avg, vari;
				for (int k = 0; k < ATTRIBUTIONS; ++k) {
					avg.a[k] = (*i)->a[k];
				}
				for (pointSet::iterator j = i + 1; j != neighbors->end(); ++j) {
					if (ufs->query((*i)->num, (*j)->num)) {
						for (int k = 0; k < ATTRIBUTIONS; ++k) {
							avg.a[k] += (*j)->a[k];
						}
						total = total + 1;
					}
				}
				for (int k = 0; k < ATTRIBUTIONS; ++k) {
					avg.a[k] /= total;
				}
				for (pointSet::iterator j = i + 1; j != neighbors->end(); ++j) {
					if (ufs->query((*i)->num, (*j)->num)) {
						for (int k = 0; k < ATTRIBUTIONS; ++k) {
							vari.a[k] += ((*j)->a[k] - avg.a[k])*((*j)->a[k] - avg.a[k]);
						}
					}
				}
				for (int k = 0; k < ATTRIBUTIONS; ++k) {
					vari.a[k] /= total;
				}
				double p = (double)total / neighbors->size();
				for (int k = 0; k < ATTRIBUTIONS; ++k) {
					if (point->a[k] < INFINITE - 1) {
						p *= exp(-(point->a[k] - avg.a[k])*(point->a[k] - avg.a[k]) / (2 * vari.a[k])) / sqrt(vari.a[k]);
					}
				}
				if (p > min_length) {
					min_length = p;
					min_p = avg.a[d];
					represent = (*i);
				}
			}
		}
		if (represent != NULL) {
			ufs->connect(point->num, represent->num);
		}
		return min_p;
	}

	void insert(Point *point, double E, UnionFindSet *ufs) {
		TREE_Point *p = root->r;
		if (p == NULL) {
			root->r = new TREE_Point();
			root->r->l = root->r->r = NULL;
			root->d = 0;
			root->point = point;
			return;
		}
		while (1) {
			if (point->a[p->d] < p->point->a[p->d]) {
				if (p->l == NULL) {
					p->l = new TREE_Point();
					p = p->l;
					p->d = rand() % ATTRIBUTIONS;
					p->l = p->r = NULL;
					p->point = point;
					update(point, ufs);
					return;
				}
				else {
					p = p->l;
				}
			}
			else {
				if (p->r == NULL) {
					p->r = new TREE_Point();
					p = p->r;
					p->d = rand() % ATTRIBUTIONS;
					p->l = p->r = NULL;
					p->point = point;
					update(point, ufs);
					return;
				}
				else {
					p = p->r;
				}
			}
		}
	}

#ifdef DEBUG
	void _traverse(TREE_Point *p) {
		if (p == NULL) {
			std::cout << "*" << std::endl;
			return;
		}
		for (int i = 0; i < ATTRIBUTIONS; ++i) {
			std::cout << p->point->a[i] << ' ';
		}
		std::cout << std::endl;
		_traverse(p->l);
		_traverse(p->r);
	}
	void traverse() {
		if (root->r == NULL) std::cout << "(Empty)" << std::endl;
		else _traverse(root->r);
	}
#endif
};

void DFS(pointSet *set, Point* x, int flag, UnionFindSet* ufs) {
	std::stack<Point*> q;
	int k = 1;
	q.push(x);
	x->flag = VISITED;
	while (!q.empty()) {
		Point* p = q.top();
		q.pop();
		for (pointSet::iterator i = p->ddrs->begin(); i != p->ddrs->end(); ++i) {
			if ((*i)->flag == NOT_VISITED) {
				(*i)->flag = VISITED;
				ufs->connect((*i)->num, x->num);
				k++;
				if ((*i)->ddrs != NULL) q.push(*i);
			}
		}
	}
}

UnionFindSet* process(pointSet *set, double E, int N) {
	UnionFindSet *ufs = new UnionFindSet(N);
	int flag = 0;
#ifdef MULTI
	for (pointSet::iterator i = set->begin(); i != set->end(); i++) {
		(*i)->flag = NOT_VISITED;
	}
#endif
#ifndef MULTI
	std::cout << "Clustering...";
#endif
	for (int i = 0; i < set->size(); ++i) {
		if (set->at(i)->flag == NOT_VISITED && set->at(i)->ddrs != NULL) {
			DFS(set, set->at(i), flag, ufs);
			flag++;
		}
	}
#ifndef MULTI
	std::cout << "[Done]" << std::endl;
#endif
	return ufs;
}

UnionFindSet* process2(pointSet *set, double E, int N) {
	UnionFindSet *ufs = new UnionFindSet(N);
	for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
		if ((*i)->Nddrs >= K) {
			for (pointSet::iterator j = (*i)->ddrs->begin(); j != (*i)->ddrs->end(); ++j) {
				if ((*j)->Nddrs >= K) {
					ufs->connect((*i)->num, (*j)->num);
				}
			}
		}
	}
	return ufs;
}

void process3(pointSet *set, double E, int N, UnionFindSet *ufs) {

	for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
		if ((*i)->Nddrs < K) {
			double d = INFINITE;
			Point *p = NULL;
			for (pointSet::iterator j = (*i)->ddrs->begin(); j != (*i)->ddrs->end(); ++j) {
				if ((*j)->Nddrs >= K && distance((*i), (*j)) < d) {
					d = distance((*i), (*j));
					p = *j;
				}
			}
			if (d < INFINITE) {
				ufs->connect((*i)->num, p->num);
			}
		}
	}

	/*
	int *visited = new int[N];
	memset(visited, 0, sizeof(visited));
	for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
		if ((*i)->Nddrs >= K) {
			//visited[(*i)->num] = 1;
			for (pointSet::iterator j = (*i)->ddrs->begin(); j != (*i)->ddrs->end(); ++j) {
				//if (!visited[(*j)->num]) {
				//	if ((*j)->Nddrs < K) visited[(*j)->num] = 1;
					ufs->connect((*i)->num, (*j)->num);
				//}
			}
		}
	}*/
}

void normalize(pointSet *set) {
	double s_max[ATTRIBUTIONS];
	double s_min[ATTRIBUTIONS];
	double num[ATTRIBUTIONS] = { 0 };
	double avg[ATTRIBUTIONS] = { 0 };
	for (int i = 0; i < ATTRIBUTIONS; ++i) {
		s_max[i] = -INFINITE;
		s_min[i] = INFINITE;
	}
	for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
		for (int j = 0; j < ATTRIBUTIONS; ++j) {
			if ((*i)->a[j] != INFINITE) {
				num[j]++;
				if (s_max[j] < (*i)->a[j]) s_max[j] = (*i)->a[j];
				if (s_min[j] > (*i)->a[j]) s_min[j] = (*i)->a[j];
				avg[j] += (*i)->a[j];
			}
		}
	}
	for (int i = 0; i < ATTRIBUTIONS; ++i) avg[i] /= num[i];
	for (pointSet::iterator p = set->begin(); p != set->end(); ++p) {
		for (int i = 0; i < ATTRIBUTIONS; ++i) {
			if ((*p)->a[i] != INFINITE) {
				(*p)->a[i] = ((*p)->a[i] - avg[i]) / (s_max[i] - s_min[i]);
			}
		}
	}
}

double accuracy(pointSet *set) {
	int cluster[MAX_CLUSTER][CLUSTER];
	int a_num[CLUSTER];
	int cluster_num[MAX_CLUSTER];
	int flag_max = 0;
	memset(cluster, 0, sizeof(cluster));
	memset(a_num, 0, sizeof(a_num));
	memset(cluster_num, 0, sizeof(cluster_num));

	for (pointSet::iterator i = set->begin(); i != set->end(); i++) {
		if ((*i)->flag != NOT_VISITED && (*i)->flag_ans != NOT_VISITED) {
			cluster[(*i)->flag][(*i)->flag_ans]++;
			a_num[(*i)->flag_ans]++;
			cluster_num[(*i)->flag]++;
			if (flag_max < (*i)->flag) flag_max = (*i)->flag;
		}
	}

	double ans = 0;
	for (int i = 0; i <= flag_max; ++i) {
		double fi = 0;
		for (int j = 0; j < CLUSTER; ++j) {
			double p = (double)cluster[i][j] / (double)cluster_num[i];
			double r = (double)cluster[i][j] / (double)a_num[j];
			double f = 2 * p*r / (p + r);
			if (fi < f) fi = f;
		}
		ans += ((double)cluster_num[i] / (double)set->size())*fi;
	}
	return ans;
}

double accuracy2(pointSet *set, UnionFindSet* ufs) {
	double a = 0, b = 0, c = 0;
	for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
		for (pointSet::iterator j = set->begin(); j != set->end(); ++j) {
			if ((*i)->flag_ans == (*j)->flag_ans) {
				if (ufs->query((*i)->num, (*j)->num)) {
					a = a + 1;
				}
				else {
					b = b + 1;
				}
			}
			else if(ufs->query((*i)->num, (*j)->num)){
				c = c + 1;
			}
		}
	}
	return 2 * a / (2 * a + b + c);
}

int Point::Number = 0;
int main(int argc, char* argv[])
{
	
	srand(1);
	double E;
	int N;
	double l, r, m;
	std::fstream fin;
#ifdef MULTI
	std::cin >> l >> r;
	fin.open("input.txt", std::fstream::in);
#else
	if (argc > 1) {
		E = atof(argv[2]);
		fin.open(argv[1], std::fstream::in);
	}
	else
	{
		fin.open("input.txt", std::fstream::in);
		std::cin >> E;
	}
	LARGE_INTEGER nFreq, nNow, nRead, nDone;
	double t_read, t_cal, t_all;
	QueryPerformanceFrequency(&nFreq);
	QueryPerformanceCounter(&nNow);
#endif
	pointSet* set = new pointSet();
	pointSet* completeSet;// = new pointSet();
	pointSet* incompleteSet[ATTRIBUTIONS + 1];
	pointSet* missingSet = new pointSet();
	for (int i = 0; i <= ATTRIBUTIONS; ++i) {
		incompleteSet[i] = new pointSet();
	}
	//std::ifstream fin("input.txt");
	std::cout << "Scanning...";
	fin >> N;
	for (int i = 0; i < N; ++i) {
		char c;
		Point* p = new Point();
		for (int j = 0; j < ATTRIBUTIONS; ++j) {
			if (!(fin >> p->a[j])) {
				fin.clear();
				do { fin >> c; } while (c != '?');
				p->incomplete++;
				p->a[j] = INFINITE;
			}
		}
		incompleteSet[p->incomplete]->push_back(p);
		if (!(fin >> p->flag_ans)) {
			fin.clear();
			do { fin >> c; } while (c != '?');
			p->flag_ans = NOT_VISITED;
		}
		/*
		if (p->incomplete == 0) {
		completeSet->push_back(p);
		}
		else {
		missingSet->push_back(p);
		}*/
		set->push_back(p);
	}
	completeSet = incompleteSet[0];
	fin.close();
	std::cout << "[Done]" << std::endl;
#ifndef MULTI
	QueryPerformanceCounter(&nRead);
#endif
	std::cout << "Normalizing...";
	normalize(set);
	std::cout << "[Done]" << std::endl;
	std::cout << "Constructing KD-Tree...";
	KD_TREE tree(completeSet);
	std::cout << "[Done]" << std::endl;
#ifdef MULTI
	for (double E = l; E < r; E += (r - l) / 10) {
		for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
			delete (*i)->ddrs;
			(*i)->ddrs = tree.neighbor(*i, E);
			if ((*i)->ddrs->size() < K) (*i)->ddrs = NULL;
		}
		process(set, E);
		std::cout << "E = " << E << ", accuracy = " << accuracy(set) << std::endl;
	}
#else

	std::cout << "Range searching...";
	for (pointSet::iterator i = completeSet->begin(); i != completeSet->end(); ++i) {
		(*i)->ddrs = tree.neighbor(*i, E);
		(*i)->Nddrs = (*i)->ddrs->size();
		/*
		if ((*i)->Nddrs < K) {
			delete (*i)->ddrs;
			(*i)->ddrs = NULL;
		}*/
	}
	std::cout << "[Done]" << std::endl;
	UnionFindSet* ufs = process2(completeSet, E, N);
	process3(completeSet, E, N, ufs);

	int sum = 0;
	for (int i = 1; i <= ATTRIBUTIONS; ++i) sum += incompleteSet[i]->size();
	std::cout << "Processing incomplete data: " << sum << " in total" << std::endl;
	int counter = 0;
	for (int k = 1; k <= ATTRIBUTIONS; ++k) {
		for (pointSet::iterator p = incompleteSet[k]->begin(); p != incompleteSet[k]->end(); p++) {
			for (int i = 0; i < ATTRIBUTIONS; ++i) {
				if ((*p)->a[i] == INFINITE) {
					(*p)->a[i] = tree.predict((*p), E, i, ufs);
					//std::cout << '[' << ++counter << '/' << sum << "] "<<(*p)->a[i] << std::endl;
				}
			}
			tree.insert(*p, E, ufs);
#ifdef DEBUG
			std::cout << sum-- << std::endl;
#endif
		}
		delete incompleteSet[k];
	}

	//process3(set, E, N, ufs);


	std::ofstream fout("output.txt");
	for (pointSet::iterator i = set->begin(); i != set->end(); ++i) {
		fout << (*i)->flag_ans << '\t' << ufs->father((*i)->num) << std::endl;
	}
	fout.close();

	QueryPerformanceCounter(&nDone);

	std::cout << "calculating accuracy...";
	//double acc = accuracy(set);
	double acc2 = accuracy2(set, ufs);
	std::cout << "[Done]" << std::endl;
	//std::cout << "accuracy = " << acc << std::endl;
	std::cout << "accuracy2 = " << acc2 << std::endl;
	t_read = (double)(nRead.QuadPart - nNow.QuadPart) / (double)nFreq.QuadPart;
	t_cal = (double)(nDone.QuadPart - nRead.QuadPart) / (double)nFreq.QuadPart;
	t_all = t_read + t_cal;
	std::cout << "Reading time:\t" << t_read << std::endl;
	std::cout << "Calculate time:\t" << t_cal << std::endl;
	std::cout << "Total time:\t" << t_all << std::endl;
	std::ofstream log_out("log.txt", std::ios::app);
	log_out << acc2 << ' ' << t_cal << std::endl;
#endif
	if (argc <= 1) {
		system("pause");
	}
	return 0;
}
