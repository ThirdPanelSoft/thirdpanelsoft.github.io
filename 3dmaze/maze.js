var canvas;
var gl;
var program;
var startTime = new Date();
var keys = {};
var queuedDelta = null;

// EDITABLE CONSTANTS
const MzX = 10; // X dimension of Maze
const MzY = 10; // Y dimension of Maze
var PICNUM = 4; // number of picture walls
var POLYNUM = 10; // number of polyhedra
var OPENNUM = 5; // number of floating opengl's
var controlFlip = 1;
POLYNUM = Math.min(POLYNUM, MzX * MzY - 4);
OPENNUM = Math.min(OPENNUM, MzX * MzY - 4 - POLYNUM);

const CLOYD_CHASE_MS = 20000;
const CLOYD_SPEED = 0.5;
const CLOYD_BG_A = './clair.webp';
const CLOYD_BG_B = './floyd.png';
var shapeFlipActive = false;
var shapeFlipRemaining = 0;
var shapeFlipTargetSign = 1;
var shapeFlipAxis = 0; // 0 = X, 1 = Y
const BASE_FRAME_MS = 1000 / 60;
const PLAYER_MOVE_SPEED = 0.025;
const PLAYER_TURN_SPEED = Math.PI / 60;
const INTRO_HEIGHT_SPEED = 0.02;
const INTRO_ROTATE_SPEED_DEG = 4;

var introComplete = false;
var targetTheta = 0;

var openplaces;
var SX, SY;
var SX1, SY1;
var maze;
var theta, dtheta;

var polypos, openpos;
var FinX, FinY;

var eyeX, eyeY;
var deyeX, deyeY;

var ratX, ratY, ratdX, ratdY, rattheta, ratdtheta;
var cloydX, cloydY, cloyddX, cloyddY, cloydtheta, cloyddtheta;

var polytheta = 0;
var height = 0;

var near = 0.01;
var far = 50.0;
var fovy = 90;
var aspect;
var eye, at, up;

var modelViewMatrix, projectionMatrix, scaleMatrix;
var modelViewMatrixLoc, projectionMatrixLoc, scaleMatrixLoc;

var NumVertices;
var elgible;

var lighting;

var texSize = 64;

var pointsArray, colorsArray, texCoordsArray;
var cloydTextureA = null;
var cloydTextureB = null;

var cloydChaseTimer = CLOYD_CHASE_MS;
var lastFrameTime = Date.now();
var gameOver = false;
var caughtBgInterval = null;

function isNear(a, b, radius) {
	return Math.abs(a - b) < radius;
}

function clampCellX(x) {
	return Math.max(0, Math.min(MzX - 1, x));
}

function clampCellY(y) {
	return Math.max(0, Math.min(MzY - 1, y));
}
function snapToQuarterTurn(angle) {
    return Math.round(angle / (Math.PI / 2)) * (Math.PI / 2);
}
function canMoveBetweenCells(x1, y1, x2, y2) {
	if (x1 === x2 && y1 === y2) return true;

	if (x1 === x2 && Math.abs(y1 - y2) === 1) {
		if (y2 > y1) {
			return maze[y1][x1][2] === 1 && maze[y2][x2][0] === 1;
		} else {
			return maze[y1][x1][0] === 1 && maze[y2][x2][2] === 1;
		}
	}

	if (y1 === y2 && Math.abs(x1 - x2) === 1) {
		if (x2 > x1) {
			return maze[y1][x1][1] === 1 && maze[y2][x2][3] === 1;
		} else {
			return maze[y1][x1][3] === 1 && maze[y2][x2][1] === 1;
		}
	}

	return false;
}

function hasLineOfSight(ax, ay, bx, by) {
	var acx = clampCellX(Math.floor(ax));
	var acy = clampCellY(Math.floor(ay));
	var bcx = clampCellX(Math.floor(bx));
	var bcy = clampCellY(Math.floor(by));

	if (acx === bcx && acy === bcy) return true;

	if (acy === bcy) {
		var stepX = acx < bcx ? 1 : -1;
		for (var x = acx; x !== bcx; x += stepX) {
			if (!canMoveBetweenCells(x, acy, x + stepX, acy)) return false;
		}
		return true;
	}

	if (acx === bcx) {
		var stepY = acy < bcy ? 1 : -1;
		for (var y = acy; y !== bcy; y += stepY) {
			if (!canMoveBetweenCells(acx, y, acx, y + stepY)) return false;
		}
		return true;
	}

	return false;
}

function getAccessibleNeighbors(cx, cy) {
	var neighbors = [];
	var walls = maze[cy][cx];

	if (cy > 0 && walls[0] === 1) neighbors.push([cx, cy - 1]);
	if (cx < MzX - 1 && walls[1] === 1) neighbors.push([cx + 1, cy]);
	if (cy < MzY - 1 && walls[2] === 1) neighbors.push([cx, cy + 1]);
	if (cx > 0 && walls[3] === 1) neighbors.push([cx - 1, cy]);

	return neighbors;
}

function bfsNextCell(startX, startY, targetX, targetY) {
	startX = clampCellX(startX);
	startY = clampCellY(startY);
	targetX = clampCellX(targetX);
	targetY = clampCellY(targetY);

	if (startX === targetX && startY === targetY) {
		return [startX, startY];
	}

	var visited = [];
	var prev = [];
	for (var y = 0; y < MzY; y++) {
		visited.push(new Array(MzX).fill(false));
		prev.push(new Array(MzX).fill(null));
	}

	var queue = [[startX, startY]];
	visited[startY][startX] = true;

	while (queue.length) {
		var node = queue.shift();
		var cx = node[0];
		var cy = node[1];

		if (cx === targetX && cy === targetY) break;

		var neighbors = getAccessibleNeighbors(cx, cy);
		for (var i = 0; i < neighbors.length; i++) {
			var nx = neighbors[i][0];
			var ny = neighbors[i][1];
			if (!visited[ny][nx]) {
				visited[ny][nx] = true;
				prev[ny][nx] = [cx, cy];
				queue.push([nx, ny]);
			}
		}
	}

	if (!visited[targetY][targetX]) return null;

	var cur = [targetX, targetY];
	var p = prev[targetY][targetX];
	while (p && !(p[0] === startX && p[1] === startY)) {
		cur = p;
		p = prev[cur[1]][cur[0]];
	}

	return cur;
}

function moveCloydToward(tx, ty, dt) {
	var dx = tx - cloydX;
	var dy = ty - cloydY;
	var dist = Math.sqrt(dx * dx + dy * dy);
	if (dist < 0.0001) return true;
	var step = CLOYD_SPEED * (dt / 1000.0);
	if (step >= dist) {
		cloydX = tx;
		cloydY = ty;
		return true;
	}

	cloydX += (dx / dist) * step;
	cloydY += (dy / dist) * step;
	return false;
}

function triggerCaught() {
	if (gameOver) return;
	gameOver = true;

	if (caughtBgInterval) {
		clearInterval(caughtBgInterval);
		caughtBgInterval = null;
	}

	document.documentElement.style.height = '100%';
	document.documentElement.style.width = '100%';
	document.body.style.margin = '0';
	document.body.style.width = '100%';
	document.body.style.height = '100%';
	document.body.style.overflow = 'hidden';
	document.body.innerHTML = '';

	var which = 0;
	function applyBg() {
		var src = (which % 2 === 0) ? CLOYD_BG_A : CLOYD_BG_B;
		document.body.style.backgroundImage = 'url("' + src + '")';
		document.body.style.backgroundRepeat = 'no-repeat';
		document.body.style.backgroundPosition = 'center center';
		document.body.style.backgroundSize = 'cover';
	}
	applyBg();
	caughtBgInterval = setInterval(function() {
		which++;
		applyBg();
	}, 300);
}

function updateCloyd(dt) {
	if (gameOver) return;

	var seesPlayer = hasLineOfSight(cloydX, cloydY, eyeX, eyeY);
	if (seesPlayer) {
		cloydChaseTimer = 0;
	} else if (cloydChaseTimer < CLOYD_CHASE_MS) {
		cloydChaseTimer += dt;
	}

	if (cloydChaseTimer < CLOYD_CHASE_MS) {
		cloyddtheta = 0;
		cloyddX = 0;
		cloyddY = 0;

		var sx = clampCellX(Math.floor(cloydX));
		var sy = clampCellY(Math.floor(cloydY));
		var tx = clampCellX(Math.floor(eyeX));
		var ty = clampCellY(Math.floor(eyeY));

		var nextCell = bfsNextCell(sx, sy, tx, ty);
		if (nextCell) {
			moveCloydToward(nextCell[0] + 0.5, nextCell[1] + 0.5, dt);
		}
	} else {
		[cloydtheta, cloydX, cloydY, cloyddtheta, cloyddX, cloyddY] = nextMove(cloydtheta, cloydX, cloydY, cloyddtheta, cloyddX, cloyddY);
		while (cloyddtheta) {
			[cloydtheta, cloydX, cloydY, cloyddtheta, cloyddX, cloyddY] = nextMove(cloydtheta, cloydX, cloydY, cloyddtheta, cloyddX, cloyddY);
		}
	}

	if (isNear(cloydX, eyeX, 0.25) && isNear(cloydY, eyeY, 0.25)) {
		triggerCaught();
	}
}

function normalizeAngle(a) {
	while (a <= -Math.PI) a += Math.PI * 2;
	while (a > Math.PI) a -= Math.PI * 2;
	return a;
}

function angleDiff(target, current) {
	return normalizeAngle(target - current);
}

function approachAngle(current, target, maxStep) {
	var diff = angleDiff(target, current);
	if (Math.abs(diff) <= maxStep) return normalizeAngle(target);
	return normalizeAngle(current + Math.sign(diff) * maxStep);
}

function queueCameraTurnFromKey(key) {
	if (shapeFlipActive) return;

	var k = String(key).toLowerCase();
	var delta = null;
	var turnFlip = (up[2] < 0) ? -1 : 1;

	if (k === "arrowup" || k === "w") {
		delta = 0;
	} else if (k === "arrowleft" || k === "a") {
		delta = turnFlip * (Math.PI / 2);
	} else if (k === "arrowright" || k === "d") {
		delta = turnFlip * (-Math.PI / 2);
	} else if (k === "arrowdown" || k === "s") {
		delta = Math.PI;
	}

	if (delta !== null) {
var base = snapToQuarterTurn(targetTheta);
targetTheta = snapToQuarterTurn(base + delta);
	}
}

function handlePlayerInput() {
	// Keep camera turning consistent even when the player is upside down.
	if (shapeFlipActive) return;

	var turnSpeed = Math.PI / 90;
	var moveSpeed = 0.025;
	var turnFlip = (up[2] < 0) ? -1 : 1;

	if (keys["ArrowLeft"] || keys["a"] || keys["A"]) {
		theta += turnFlip * turnSpeed;
	}
	if (keys["ArrowRight"] || keys["d"] || keys["D"]) {
		theta -= turnFlip * turnSpeed;
	}

	var dx = 0;
	var dy = 0;

	if (keys["ArrowUp"] || keys["w"] || keys["W"]) {
		dx += Math.cos(theta) * moveSpeed;
		dy += Math.sin(theta) * moveSpeed;
	}
	if (keys["ArrowDown"] || keys["s"] || keys["S"]) {
		dx -= Math.cos(theta) * moveSpeed;
		dy -= Math.sin(theta) * moveSpeed;
	}

	tryMove(dx, dy);
}

function updateIntroAnimation(dt) {
	var scale = dt / BASE_FRAME_MS;

	if (height < 3 / 4) {
		height = Math.min(3 / 4, height + INTRO_HEIGHT_SPEED * scale);
		return;
	}

	if (Math.abs(Math.abs(up[2]) - 1) > 0.0001) {
		var rot = INTRO_ROTATE_SPEED_DEG * scale;

		if (((Math.round(theta / Math.PI * 180 * 10000) / 10000 % 360 / 90) + 5) % 2) {
			up = vec3(mult(rotateX(rot), vec4(up)));
		} else {
			up = vec3(mult(rotateY(rot), vec4(up)));
		}
		return;
	}

	introComplete = true;
	targetTheta = theta;
}

function updatePlayerNavigation(dt) {
	if (!introComplete) {
		updateIntroAnimation(dt);
		return;
	}

	// Pause player movement and turning while a shape flip animation is running.
	if (shapeFlipActive) return;

	var scale = dt / BASE_FRAME_MS;
	var turnStep = PLAYER_TURN_SPEED * scale;

	var diff = angleDiff(targetTheta, theta);
	if (Math.abs(diff) > 0.001) {
		theta = approachAngle(theta, targetTheta, turnStep);
		return;
	}

	theta = snapToQuarterTurn(targetTheta);

	var moveStep = PLAYER_MOVE_SPEED * scale;
	var dx = Math.cos(theta) * moveStep;
	var dy = Math.sin(theta) * moveStep;
	tryMove(dx, dy);
}

var texCoord = [
	[
		vec2(0, 0),
		vec2(0, 1),
		vec2(1, 1),
		vec2(1, 0)
	],
	[
		vec2(0, 0),
		vec2(0, MzX),
		vec2(MzY, MzX),
		vec2(MzY, 0)
	],
];

var vertexColors = [
	vec4(0.0, 0.0, 0.0, 1.0),  // black
	vec4(1.0, 0.0, 0.0, 1.0),  // red
	vec4(1.0, 1.0, 0.0, 1.0),  // yellow
	vec4(0.0, 1.0, 0.0, 1.0),  // green
	vec4(0.0, 0.0, 1.0, 1.0),  // blue
	vec4(1.0, 0.0, 1.0, 1.0),  // magenta
	vec4(0.0, 1.0, 1.0, 1.0),  // cyan
	vec4(1.0, 1.0, 1.0, 1.0),  // white
];

var polyvert = [[
	[0,0,1.225,1], 
	[-0.5774,-1.000,-0.4082,1], 
	[-0.5774,1.000,-0.4082,1], 
	[1.155,0,-0.4082,1]],

	[[-1.414,0,0,1], 
	[0,1.414,0,1], 
	[0,0,-1.414,1], 
	[0,0,1.414,1], 
	[0,-1.414,0,1], 
	[1.414,0,0,1]],

	[[0,0,-1.902,1], 
	[0,0,1.902,1], 
	[-1.701,0,-0.8507,1], 
	[1.701,0,0.8507,1], 
	[1.376,-1.000,-0.8507,1], 
	[1.376,1.000,-0.8507,1], 
	[-1.376,-1.000,0.8507,1], 
	[-1.376,1.000,0.8507,1], 
	[-0.5257,-1.618,-0.8507,1], 
	[-0.5257,1.618,-0.8507,1], 
	[0.5257,-1.618,0.8507,1], 
	[0.5257,1.618,0.8507,1]],

	[[-2.753,0,0.5257,1], 
	[2.753,0,-0.5257,1], 
	[-0.8507,-2.618,0.5257,1], 
	[-0.8507,2.618,0.5257,1], 
	[2.227,-1.618,0.5257,1], 
	[2.227,1.618,0.5257,1], 
	[-0.5257,-1.618,2.227,1], 
	[-0.5257,1.618,2.227,1], 
	[-1.376,-1.000,-2.227,1], 
	[-1.376,1.000,-2.227,1], 
	[1.376,-1.000,2.227,1], 
	[1.376,1.000,2.227,1], 
	[1.701,0,-2.227,1], 
	[-2.227,-1.618,-0.5257,1], 
	[-2.227,1.618,-0.5257,1], 
	[-1.701,0,2.227,1], 
	[0.5257,-1.618,-2.227,1], 
	[0.5257,1.618,-2.227,1], 
	[0.8507,-2.618,-0.5257,1], 
	[0.8507,2.618,-0.5257,1]]]

var polyind = [
	[1,2,3,2,1,0,3,0,1,0,3,2],
	[3,4,5,3,5,1,3,1,0,3,0,4,4,0,2,4,2,5,2,0,1,5,2,1],
	[1,11,7,1,7,6,1,6,10,1,10,3,1,3,11,4,8,0,5,4,0,9,5,0,2,9,0,8,2,0,11,9,7,7,2,6,6,8,10,10,4,3,3,5,11,4,10,8,5,3,4,9,11,5,2,7,9,8,6,2],
	[14,9,8,14,8,13,14,13,0,1,5,11,1,11,10,1,10,4,4,10,6,4,6,2,4,2,18,10,11,7,10,7,15,10,15,6,11,5,19,11,19,3,11,3,7,5,1,12,5,12,17,5,17,19,1,4,18,1,18,16,1,16,12,3,19,17,3,17,9,3,9,14,17,12,16,17,16,8,17,8,9,16,18,2,16,2,13,16,13,8,2,6,15,2,15,0,2,0,13,15,7,3,15,3,14,15,14,0]
]

function resizeCanvas() {
	canvas.width = window.innerWidth;
	canvas.height = window.innerHeight;
	gl.viewport(0, 0, canvas.width, canvas.height);
	aspect = canvas.width / canvas.height;
}

window.addEventListener("keydown", function (e) {
	keys[e.key] = true;

	if (
		e.key === "ArrowUp" || e.key === "ArrowDown" || e.key === "ArrowLeft" || e.key === "ArrowRight" ||
		e.key === "w" || e.key === "a" || e.key === "s" || e.key === "d" ||
		e.key === "W" || e.key === "A" || e.key === "S" || e.key === "D"
	) {
		e.preventDefault();
		if (!e.repeat) {
			queueCameraTurnFromKey(e.key);
		}
	}
});

window.addEventListener("keyup", function (e) {
	keys[e.key] = false;

	if (
		e.key === "ArrowUp" || e.key === "ArrowDown" || e.key === "ArrowLeft" || e.key === "ArrowRight" ||
		e.key === "w" || e.key === "a" || e.key === "s" || e.key === "d" ||
		e.key === "W" || e.key === "A" || e.key === "S" || e.key === "D"
	) {
		e.preventDefault();
	}
});

window.onload = function() {
	canvas = document.getElementById("gl-canvas");

	gl = WebGLUtils.setupWebGL(canvas);
	if (!gl) { alert("WebGL isn't available"); }

	window.addEventListener('resize', resizeCanvas, false);
	resizeCanvas();

	gl.clearColor(0, 0, 0, 1.0);
	gl.enable(gl.DEPTH_TEST);

	gl.enable(gl.BLEND);
	gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);

	//
	//  Load shaders and initialize attribute buffers
	//
	program = initShaders(gl, "vertex-shader", "fragment-shader");
	gl.useProgram(program);

	resetVars();

	gl.enable(gl.CULL_FACE);

	modelViewMatrixLoc = gl.getUniformLocation(program, "modelViewMatrix");
	projectionMatrixLoc = gl.getUniformLocation(program, "projectionMatrix");
	scaleMatrixLoc = gl.getUniformLocation(program, "scaleMatrix");

	gl.uniform1i(gl.getUniformLocation(program, "wall"), 0);
	gl.uniform1i(gl.getUniformLocation(program, "floor"), 1);
	gl.uniform1i(gl.getUniformLocation(program, "ceiling"), 2);
	gl.uniform1i(gl.getUniformLocation(program, "pic"), 3);
	gl.uniform1i(gl.getUniformLocation(program, "start"), 4);
	gl.uniform1i(gl.getUniformLocation(program, "fin"), 5);
	gl.uniform1i(gl.getUniformLocation(program, "open"), 6);
	gl.uniform1i(gl.getUniformLocation(program, "rat"), 7);
	gl.uniform1i(gl.getUniformLocation(program, "cloyd"), 9);
	//
	// Initialize textures
	//

	const wallImg = new Image();
	wallImg.onload = function() {
		const wallTexture = gl.createTexture();
		gl.activeTexture(gl.TEXTURE0);
		gl.bindTexture(gl.TEXTURE_2D, wallTexture);
		gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGB, gl.RGB, gl.UNSIGNED_BYTE, wallImg);
		gl.generateMipmap(gl.TEXTURE_2D);

		const floorImg = new Image();
		floorImg.onload = function() {
			const floorTexture = gl.createTexture();
			gl.activeTexture(gl.TEXTURE0 + 1);
			gl.bindTexture(gl.TEXTURE_2D, floorTexture);
			gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGB, gl.RGB, gl.UNSIGNED_BYTE, floorImg);
			gl.generateMipmap(gl.TEXTURE_2D);

			const ceilingImg = new Image();
			ceilingImg.onload = function() {
				const ceilingTexture = gl.createTexture();
				gl.activeTexture(gl.TEXTURE0 + 2);
				gl.bindTexture(gl.TEXTURE_2D, ceilingTexture);
				gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGB, gl.RGB, gl.UNSIGNED_BYTE, ceilingImg);
				gl.generateMipmap(gl.TEXTURE_2D);
				gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);

				const picImg = new Image();
				picImg.onload = function() {
					const picTexture = gl.createTexture();
					gl.activeTexture(gl.TEXTURE0 + 3);
					gl.bindTexture(gl.TEXTURE_2D, picTexture);
					gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGB, gl.RGB, gl.UNSIGNED_BYTE, picImg);
					gl.generateMipmap(gl.TEXTURE_2D);
					gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);

					const startImg = new Image();
					startImg.onload = function() {
						const startTexture = gl.createTexture();
						gl.activeTexture(gl.TEXTURE0 + 4);
						gl.bindTexture(gl.TEXTURE_2D, startTexture);
						gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, startImg);
						gl.generateMipmap(gl.TEXTURE_2D);
						gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);

						const finImg = new Image();
						finImg.onload = function() {
							const finTexture = gl.createTexture();
							gl.activeTexture(gl.TEXTURE0 + 5);
							gl.bindTexture(gl.TEXTURE_2D, finTexture);
							gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, finImg);
							gl.generateMipmap(gl.TEXTURE_2D);
							gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);

							const openImg = new Image();
							openImg.onload = function() {
								const openTexture = gl.createTexture();
								gl.activeTexture(gl.TEXTURE0 + 6);
								gl.bindTexture(gl.TEXTURE_2D, openTexture);
								gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, openImg);
								gl.generateMipmap(gl.TEXTURE_2D);
								gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);

								const ratImg = new Image();
								ratImg.onload = function() {
									const ratTexture = gl.createTexture();
									gl.activeTexture(gl.TEXTURE0 + 7);
									gl.bindTexture(gl.TEXTURE_2D, ratTexture);
									gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, ratImg);
									gl.generateMipmap(gl.TEXTURE_2D);
									gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);

									const cloydImg = new Image();
									cloydImg.onload = function() {
										cloydTextureA = gl.createTexture();
										gl.activeTexture(gl.TEXTURE0 + 9);
										gl.bindTexture(gl.TEXTURE_2D, cloydTextureA);
										gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, cloydImg);

										if ((cloydImg.width & (cloydImg.width - 1)) === 0 && (cloydImg.height & (cloydImg.height - 1)) === 0) {
											gl.generateMipmap(gl.TEXTURE_2D);
											gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
											gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
											gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
										} else {
											gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
											gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
											gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
											gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
										}

										const cloydAltImg = new Image();
										cloydAltImg.onload = function() {
											cloydTextureB = gl.createTexture();
											gl.activeTexture(gl.TEXTURE0 + 9);
											gl.bindTexture(gl.TEXTURE_2D, cloydTextureB);
											gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, cloydAltImg);

											if ((cloydAltImg.width & (cloydAltImg.width - 1)) === 0 && (cloydAltImg.height & (cloydAltImg.height - 1)) === 0) {
												gl.generateMipmap(gl.TEXTURE_2D);
												gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
												gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
												gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
											} else {
												gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
												gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
												gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
												gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
											}

											render();
										};
										cloydAltImg.src = './floyd.png';
									};
									cloydImg.src = './clair.webp';
								};
								ratImg.src = './rat.png';
							};
							openImg.src = './gl.png';
						};
						finImg.src = './fin.png';
					};
					startImg.src = './start2.png';
				};
				picImg.src = './pic.bmp';
			};
			ceilingImg.src = './ceiling2.bmp';
		};
		floorImg.src = './floor.bmp';
	};
	wallImg.src = './wall.bmp';
};

function resetVars() {
    lighting = 0;
    gameOver = false;
    introComplete = false;
    targetTheta = 0;
    keys = {};
    cloydChaseTimer = CLOYD_CHASE_MS;
    lastFrameTime = Date.now();

    // Reset shape flip state
    shapeFlipActive = false;
    shapeFlipRemaining = 0;
    shapeFlipTargetSign = 1;
    shapeFlipAxis = 0;

	if (caughtBgInterval) {
		clearInterval(caughtBgInterval);
		caughtBgInterval = null;
	}
	if (document && document.body) {
		document.body.style.backgroundImage = '';
		document.body.style.backgroundRepeat = '';
		document.body.style.backgroundPosition = '';
		document.body.style.backgroundSize = '';
		document.body.style.overflow = '';
		document.body.style.margin = '';
	}
	if (document && document.documentElement) {
		document.documentElement.style.height = '';
		document.documentElement.style.width = '';
	}

	maze = newMaze(MzX, MzY);

	SX = 0;
	SY = 0;

	openplaces = [];
	for (var i = 0; i < MzX; i++) {
		for (var j = 0; j < MzY; j++) {
			openplaces.push([i, j]);
		}
	}
	[SX, SY] = openplaces.splice(Math.floor(Math.random() * openplaces.length), 1)[0];

	eyeX = SX + .5;
	eyeY = SY + .5;
	deyeX = 0;
	deyeY = 0;
	dtheta = 0;

	SX1 = SX;
	SY1 = SY;

	ratdX = 0;
	ratdY = 0;
	rattheta = 0;
	ratdtheta = 0;

	cloyddX = 0;
	cloyddY = 0;
	cloydtheta = 0;
	cloyddtheta = 0;

	// don't start facing a wall
	if (maze[SY][SX][1] != 1) {
		if (maze[SY][SX][0] == 1) {
			theta = -90 / 180 * Math.PI;
			SY1 = SY - 1;
		} else if (maze[SY][SX][2] == 1) {
			theta = 90 / 180 * Math.PI;
			SY1 = SY + 1;
		} else {
			theta = Math.PI;
			SX1 = SX - 1;
		}
	} else {
		theta = 0;
		SX1 = SX + 1;
	}

	targetTheta = theta;

	for (var i = 0; i < openplaces.length; i++) {
		if (openplaces[i][0] == SX1 && openplaces[i][1] == SY1) {
			openplaces.splice(i, 1);
			break;
		}
	}

	polypos = [];
	for (var i = 0; i < POLYNUM; i++) {
		polypos.push(openplaces.splice(Math.floor(Math.random() * openplaces.length), 1)[0].concat([Math.floor(Math.random() * 4)]));
	}

	openpos = [];
	for (var i = 0; i < OPENNUM; i++) {
		openpos.push(openplaces.splice(Math.floor(Math.random() * openplaces.length), 1)[0]);
	}

	[FinX, FinY] = openplaces.splice(Math.floor(Math.random() * openplaces.length), 1)[0];

	[ratX, ratY] = openplaces.splice(Math.floor(Math.random() * openplaces.length), 1)[0];
	ratX += .5;
	ratY += .5;

	[cloydX, cloydY] = openplaces.splice(Math.floor(Math.random() * openplaces.length), 1)[0];
	cloydX += .5;
	cloydY += .5;

	up = vec3(0.0, 0.0, 1.0);

	NumVertices = 0;
	elgible = [];
	for (var i = 0; i < maze.length; i++) {
		for (var j = 0; j < maze[0].length; j++) {
			for (var k = 0; k < 4; k++) {
				if (!maze[i][j][k]) {
					NumVertices += 6;
					elgible.push([i, j, k]);
				}
			}
		}
	}

	var picCount = Math.min(PICNUM, elgible.length);
	for (var i = 0; i < picCount; i++) {
		var pos = elgible.splice(Math.floor(Math.random() * elgible.length), 1)[0];
		maze[pos[0]][pos[1]][pos[2]] = 3;
	}

	pointsArray = [];
	colorsArray = [];
	texCoordsArray = [];

	mazevertices();

	//
	//  Load shaders and initialize attribute buffers
	//
	gl.useProgram(program);

	var cBuffer = gl.createBuffer();
	gl.bindBuffer(gl.ARRAY_BUFFER, cBuffer);
	gl.bufferData(gl.ARRAY_BUFFER, flatten(colorsArray), gl.STATIC_DRAW);

	var vColor = gl.getAttribLocation(program, "vColor");
	gl.vertexAttribPointer(vColor, 4, gl.FLOAT, false, 0, 0);
	gl.enableVertexAttribArray(vColor);

	var vBuffer = gl.createBuffer();
	gl.bindBuffer(gl.ARRAY_BUFFER, vBuffer);
	gl.bufferData(gl.ARRAY_BUFFER, flatten(pointsArray), gl.STATIC_DRAW);

	var vPosition = gl.getAttribLocation(program, "vPosition");
	gl.vertexAttribPointer(vPosition, 4, gl.FLOAT, false, 0, 0);
	gl.enableVertexAttribArray(vPosition);

	var tBuffer = gl.createBuffer();
	gl.bindBuffer(gl.ARRAY_BUFFER, tBuffer);
	gl.bufferData(gl.ARRAY_BUFFER, flatten(texCoordsArray), gl.STATIC_DRAW);

	var vTexCoord = gl.getAttribLocation(program, "vTexCoord");
	gl.vertexAttribPointer(vTexCoord, 2, gl.FLOAT, false, 0, 0);
	gl.enableVertexAttribArray(vTexCoord);
}

function mazevertices() {
	quad([MzX, 0, 0, 1], [MzX, MzY, 0, 1], [0, MzY, 0, 1], [0, 0, 0, 1], 1, 0);
	quad([0, 0, 1, 1], [0, MzY, 1, 1], [MzX, MzY, 1, 1], [MzX, 0, 1, 1], 1, 0);

	// [top, right, bottom, left]
	for (var i = 0; i < maze.length; i++) {
		for (var j = 0; j < maze[0].length; j++) {
			var vertices = [
				vec4(j, i, 1.0, 1.0),
				vec4(j, i + 1, 1.0, 1.0),
				vec4(j + 1, i + 1, 1.0, 1.0),
				vec4(j + 1, i, 1.0, 1.0),
				vec4(j, i, 0.0, 1.0),
				vec4(j, i + 1, 0.0, 1.0),
				vec4(j + 1, i + 1, 0.0, 1.0),
				vec4(j + 1, i, 0.0, 1.0)
			];
			if (!maze[i][j][0])
				quad(vertices[0], vertices[3], vertices[7], vertices[4], 0, 1);
			if (!maze[i][j][1])
				quad(vertices[6], vertices[7], vertices[3], vertices[2], 0, 0);
			if (!maze[i][j][2])
				quad(vertices[5], vertices[6], vertices[2], vertices[1], 0, 0);
			if (!maze[i][j][3])
				quad(vertices[4], vertices[5], vertices[1], vertices[0], 0, 0);
			if (maze[i][j][0] == 3)
				quad(vertices[0], vertices[3], vertices[7], vertices[4], 3, 1);
			if (maze[i][j][1] == 3)
				quad(vertices[6], vertices[7], vertices[3], vertices[2], 3, 0);
			if (maze[i][j][2] == 3)
				quad(vertices[5], vertices[6], vertices[2], vertices[1], 3, 0);
			if (maze[i][j][3] == 3)
				quad(vertices[4], vertices[5], vertices[1], vertices[0], 3, 0);
		}
	}

	quad([0, .5, 0, 1], [0, -.5, 0, 1], [0, -.5, 1, 1], [0, .5, 1, 1], 0, 0);

	for (var i = 0; i < polyind.length; ++i) {
		for (var j = 0; j < polyind[i].length; ++j) {
			var scales = [0.20, 0.15, 0.13, 0.10];

			point = mult(
				scalem(scales[i], scales[i], scales[i]),
				polyvert[i][polyind[i][j]]
			);
			pointsArray.push(point);
			var faceCount = polyind[i].length / 3;
			var face = Math.floor(j / 3);
			var shade = 0.03 + 0.15 * face / (faceCount - 1);

			colorsArray.push([shade, shade, shade, 1]);
			texCoordsArray.push(texCoord[0][j % 3]);
		}
	}
}

function quad(a, b, c, d, t, f) {
	// t0 = wall, t1=floor/ceilings, t3=pic
	// f0 = dont flip, f1=flip

	var indices = [a, b, c, a, c, d];
	var indices2 = [1, 2, 3, 1, 3, 0];

	if (t == 3) {
		for (var i = 0; i < indices.length; ++i) {
			pointsArray.splice(12 + i, 0, indices[i]);
			colorsArray.splice(12 + i, 0, vertexColors[7]);
			texCoordsArray.splice(12 + i, 0, texCoord[0][(indices2[i] + 2 * (f)) % 4]);
		}
		return;
	}

	for (var i = 0; i < indices.length; ++i) {
		pointsArray.push(indices[i]);
		colorsArray.push(vertexColors[7]);
		texCoordsArray.push(texCoord[t][(indices2[i] + 2 * (f && !t)) % 4]);
	}
}

function tryMove(dx, dy) {
	var nx = eyeX + dx;
	var ny = eyeY + dy;

	if (canMoveTo(nx, eyeY)) {
		eyeX = nx;
	}
	if (canMoveTo(eyeX, ny)) {
		eyeY = ny;
	}
}

const PLAYER_RADIUS = 0.25;
function canMoveTo(nx, ny) {
	if (nx < 0 || ny < 0 || nx >= MzX || ny >= MzY) {
		return false;
	}

	let cellX = Math.floor(nx);
	let cellY = Math.floor(ny);

	let localX = nx - cellX; // 0..1 inside cell
	let localY = ny - cellY;

	let walls = maze[cellY][cellX];

	// walls = [top, right, bottom, left]
	if (walls[0] !== 1 && localY < PLAYER_RADIUS)
		return false;

	if (walls[2] !== 1 && localY > 1 - PLAYER_RADIUS)
		return false;

	if (walls[3] !== 1 && localX < PLAYER_RADIUS)
		return false;

	if (walls[1] !== 1 && localX > 1 - PLAYER_RADIUS)
		return false;

	return true;
}

function bindCloydTexture() {
	if (!cloydTextureA || !cloydTextureB) return;

	var useAlt =
		Math.floor((Date.now() - startTime.getTime()) / 300) % 2;

	gl.activeTexture(gl.TEXTURE0 + 9);
	gl.bindTexture(gl.TEXTURE_2D,
		useAlt ? cloydTextureB : cloydTextureA);
}
function startShapeFlip() {
	if (shapeFlipActive) return;

	shapeFlipActive = true;
	shapeFlipRemaining = 180; // degrees for a full flip
	shapeFlipTargetSign = (up[2] >= 0) ? -1 : 1;

	// Keep the flip axis consistent with the current camera orientation,
	// matching the logic already used elsewhere in the file.
	shapeFlipAxis = (((Math.round(theta / Math.PI * 180 * 10000) / 10000 % 360 / 90) + 5) % 2) ? 0 : 1;
}

function updateShapeFlip(dt) {
	if (!shapeFlipActive) return;

	var scale = dt / BASE_FRAME_MS;
	var step = INTRO_ROTATE_SPEED_DEG * scale;
	var rot = Math.min(step, shapeFlipRemaining);

	if (shapeFlipAxis === 0) {
		up = vec3(mult(rotateX(rot), vec4(up)));
	} else {
		up = vec3(mult(rotateY(rot), vec4(up)));
	}

	shapeFlipRemaining -= rot;

	if (shapeFlipRemaining <= 0.001) {
		up = vec3(0.0, 0.0, shapeFlipTargetSign);
		shapeFlipActive = false;
	}
}
var render = function() {
	if (gameOver) return;

	var now = Date.now();
	var dt = now - lastFrameTime;
	lastFrameTime = now;
	if (dt < 0 || dt > 1000) dt = 16;

	gl.uniform1i(gl.getUniformLocation(program, "lighting"), lighting);

	gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

	eye = vec3(eyeX, eyeY, 1 / 3);
	at = add(eye, vec3(Math.cos(theta), Math.sin(theta), 0));

	modelViewMatrix = lookAt(eye, at, up);
	projectionMatrix = perspective(fovy, aspect, near, far);
	scaleMatrix = scalem(1, 1, 3 / 4);

	gl.uniformMatrix4fv(modelViewMatrixLoc, false, flatten(modelViewMatrix));
	gl.uniformMatrix4fv(projectionMatrixLoc, false, flatten(projectionMatrix));
	gl.uniformMatrix4fv(scaleMatrixLoc, false, flatten(scaleMatrix));

	gl.uniform4f(gl.getUniformLocation(program, "cameraPos"), eyeX, eyeY, 1 / 3, 1);

	// Advance the flip animation first, then keep the player frozen while it runs.
	var wasFlipping = shapeFlipActive;
	updateShapeFlip(dt);

	// floor
	gl.uniform1i(gl.getUniformLocation(program, "i"), 1);
	gl.drawArrays(gl.TRIANGLES, 0, 6);

	// ceiling
	gl.uniform1i(gl.getUniformLocation(program, "i"), 2);
	gl.drawArrays(gl.TRIANGLES, 6, 6);

	if (isNear(eyeX, FinX + 0.5, 0.4) && isNear(eyeY, FinY + 0.5, 0.4)) {
		height -= .02;
		scaleMatrix = scalem(1, 1, height);
		gl.uniformMatrix4fv(scaleMatrixLoc, false, flatten(scaleMatrix));

		if (height < 0) {
			resetVars();
			requestAnimFrame(render);
			return;
		}
	} else {
		if (!wasFlipping) {
			updatePlayerNavigation(dt);
		}
		scaleMatrix = scalem(1, 1, height);
		gl.uniformMatrix4fv(scaleMatrixLoc, false, flatten(scaleMatrix));
	}

	for (let i = 0; i < 4; i++) {
		[rattheta, ratX, ratY, ratdtheta, ratdX, ratdY] =
			nextMove(rattheta, ratX, ratY, ratdtheta, ratdX, ratdY);

		while (ratdtheta)
			[rattheta, ratX, ratY, ratdtheta, ratdX, ratdY] =
				nextMove(rattheta, ratX, ratY, ratdtheta, ratdX, ratdY);
	}
	updateCloyd(dt);
	if (gameOver) return;

	//--------------------------------------------------
	// OPAQUE GEOMETRY
	//--------------------------------------------------

	// picture walls
	gl.uniform1i(gl.getUniformLocation(program, "i"), 3);
	gl.drawArrays(gl.TRIANGLES, 12, PICNUM * 6);

	// maze walls
	gl.uniform1i(gl.getUniformLocation(program, "i"), 0);
	gl.drawArrays(gl.TRIANGLES, 12 + PICNUM * 6, NumVertices - PICNUM * 6);

	// polyhedra
	gl.uniform1i(gl.getUniformLocation(program, "i"), 8);

	polytheta += 2;

	for (i = 0; i < polypos.length; i++) {

		scaleMatrix = mult(
			scalem(1, 1, 3 / 4),
			mult(
				translate(polypos[i][0] + .5, polypos[i][1] + .5, .25),
				rotateZ(polytheta)
			)
		);

		gl.uniformMatrix4fv(scaleMatrixLoc, false, flatten(scaleMatrix));

		gl.drawArrays(
			gl.TRIANGLES,
			[12, 24, 48, 108][polypos[i][2]] + 6 + NumVertices,
			[12, 24, 60, 108][polypos[i][2]]
		);

if (
	isNear(eyeX, polypos[i][0] + 0.5, 0.4) &&
	isNear(eyeY, polypos[i][1] + 0.5, 0.4)
) {
	startShapeFlip();
	polypos.splice(i, 1);
	i--;
}
	}

	//--------------------------------------------------
	// TRANSPARENT BILLBOARDS
	//--------------------------------------------------

	gl.depthMask(false);
	gl.disable(gl.CULL_FACE);

	var sprites = [];

	sprites.push({
		type: 4,
		x: SX1 + .5,
		y: SY1 + .5
	});

	sprites.push({
		type: 5,
		x: FinX + .5,
		y: FinY + .5
	});

	sprites.push({
		type: 7,
		x: ratX,
		y: ratY
	});

	sprites.push({
		type: 9,
		x: cloydX,
		y: cloydY
	});

	for (i = 0; i < openpos.length; i++) {
		sprites.push({
			type: 6,
			x: openpos[i][0] + .5,
			y: openpos[i][1] + .5
		});
	}

	// sort farthest first
	sprites.sort(function(a, b) {

		var da =
			(eyeX - a.x) * (eyeX - a.x) +
			(eyeY - a.y) * (eyeY - a.y);

		var db =
			(eyeX - b.x) * (eyeX - b.x) +
			(eyeY - b.y) * (eyeY - b.y);

		return db - da;
	});

	for (i = 0; i < sprites.length; i++) {

		var s = sprites[i];

		gl.uniform1i(gl.getUniformLocation(program, "i"), s.type);

		if (s.type === 9)
			bindCloydTexture();

		var zScale = 0.75;
		var zTranslate = 0;

		if (s.type === 9 && up[2] < 0) {
			zScale = -0.75;        // Flip vertically (invert Z)
			zTranslate = 0.75;     // Shift up so the sprite rests on the floor
		}

		scaleMatrix = mult(
			scalem(1, 1, height),
			mult(
				translate(s.x, s.y, zTranslate),
				mult(
					rotateZ(theta / Math.PI * 180),
					scalem(0.75, 0.75, zScale)
				)
			)
		);
		gl.uniformMatrix4fv(
			scaleMatrixLoc,
			false,
			flatten(scaleMatrix)
		);

		gl.drawArrays(gl.TRIANGLES, NumVertices + 12, 6);
	}

	gl.enable(gl.CULL_FACE);
	gl.depthMask(true);

	requestAnimFrame(render);
}

function nextMove(theta, X, Y, dtheta, dX, dY) {
	var degtheta = Math.round(theta / Math.PI * 180 * 10000) / 10000;
	X = Math.round(X * 10000) / 10000;
	Y = Math.round(Y * 10000) / 10000;
	if (degtheta % 90) {
		return [theta + dtheta, X, Y, dtheta, dX, dY];
	} else if ((X + .5) % 1 || (Y + .5) % 1) {
		return [theta, X + dX, Y + dY, dtheta, dX, dY];
	} else { // new move
		var direction = ((degtheta % 360 / 90) + 5) % 4;
		var walls = maze[Y - .5][X - .5];
		// [-Y,+X,+Y,-X]
		// [ 0, 1, 2, 3]
		// turn right = theta minus = <--
		//
		// strategy:
		// just-turned and front=open - forward
		// right=open - rotate right
		// front=open - forward
		// left=open - rotate left
		// else i.e. dead end - rotate right
		if (dtheta && walls[direction] == 1) {
			dX = ((direction == 1) - (direction == 3)) / 100;
			dY = ((direction == 2) - (direction == 0)) / 100;
			return [theta, X + dX, Y + dY, 0, dX, dY];
		} else if (walls[(direction + 3) % 4] == 1) {
			dtheta = -1 * Math.PI / 180.0;
			return [theta + dtheta, X, Y, dtheta, 0, 0];
		} else if (walls[direction] == 1) {
			dX = ((direction == 1) - (direction == 3)) / 100;
			dY = ((direction == 2) - (direction == 0)) / 100;
			return [theta, X + dX, Y + dY, 0, dX, dY];
		} else if (walls[(direction + 1) % 4] == 1) {
			dtheta = 1 * Math.PI / 180.0;
			return [theta + dtheta, X, Y, dtheta, 0, 0];
		} else {
			dtheta = -1 * Math.PI / 180.0;
			return [theta + dtheta, X, Y, dtheta, 0, 0];
		}
	}
}

function newMaze(x, y) { // https://www.dstromberg.com/2013/07/tutorial-random-maze-generation-algorithm-in-javascript/
	var totalCells = x * y;
	var cells = new Array();
	var unvis = new Array();

	// initilize arrays
	for (var i = 0; i < y; i++) {
		cells[i] = new Array();
		unvis[i] = new Array();
		for (var j = 0; j < x; j++) {
			cells[i][j] = [0, 0, 0, 0];
			unvis[i][j] = true;
		}
	}

	// set starting position
	var currentCell = [Math.floor(Math.random() * y), Math.floor(Math.random() * x)];

	var path = [currentCell];
	unvis[currentCell[0]][currentCell[1]] = false;
	var visited = 1;

	while (visited < totalCells) {
		// generate array of valid unvisited neighbor cells
		var potential = [[currentCell[0] - 1, currentCell[1], 0, 2],	// top
			[currentCell[0], currentCell[1] + 1, 1, 3],	// right
			[currentCell[0] + 1, currentCell[1], 2, 0],	// bottom
			[currentCell[0], currentCell[1] - 1, 3, 1]];	// left
		var neighbors = new Array();
		for (var l = 0; l < 4; l++) {
			if (potential[l][0] > -1 && potential[l][0] < y && potential[l][1] > -1 && potential[l][1] < x && unvis[potential[l][0]][potential[l][1]]) {
				neighbors.push(potential[l]);
			}
		}
		// remove the border to a neighboring cell and visit it
		if (neighbors.length) {
			var next = neighbors[Math.floor(Math.random() * neighbors.length)];
			cells[currentCell[0]][currentCell[1]][next[2]] = 1;
			cells[next[0]][next[1]][next[3]] = 1;

			unvis[next[0]][next[1]] = false;
			visited++;

			currentCell = [next[0], next[1]];
			path.push(currentCell);
		} else {
			currentCell = path.pop();
		}
	}

	return cells;
}
